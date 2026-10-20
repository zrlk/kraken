/-
The x64 Treiber pilot with a `dmem` call stack: the whole-program theorem.

`pilotX` (`Lower/PilotX64Prog.lean`) keeps its call stack in `dmem`; its EnvG
premise is `hthr_pX` (`Lower/PilotX64Link.lean`). This file adds the second
VC pass that the value-restricted bridge needs and assembles the theorem.

* `push_specI`, `pop_specI`, `main_specI`: the text's judgments in
  `IX P = counted (relInvX (SL P) (GV P))` — every shared access is at a
  location of `SL P` and every value stored is in `GV P`; no ownership facts.
* `pilotXPure`, `pilotXPure_holds`: the purity specification
  (`RelPureSpecQX`) of the text and its `HoldsV` at each thread's start.
* `pilotX_promising`: the whole program on `Reachable Arch.tso fuel`, via
  `Vals.envGValsBridgeX_ofPure` (`Lower/KitX64ValsPure.lean`); hypotheses are
  start facts only.
-/
import Kraken.Promising.Lower.PilotX64Link
import Kraken.Promising.Lower.KitX64ValsPure

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- Thread code's value-restricted purity environment at `P`, counted. -/
abbrev IX (P : Params) : SharedEnv := SharedEnv.counted (relInvX (SL P) (GV P))

/-! ## Helpers -/

/-- A combined load at a heap address in `IX P`: an answer in `GV P`, the
counter moved. -/
theorem ldI {P : Params} {H : BitVec 64 → Prop} {d : Mem 64} {a x : BitVec 64} {g g' : (IX P).State}
    (hH : HeapOff H d) (ha : H a)
    (h : (∃ v, Mem.loadInt d a 8 = some v ∧ x = BitVec.ofInt 64 v ∧ g' = g) ∨ (Mem.loadInt d a 8 = none ∧
      ∃ v, (IX P).step (.load .plain false a 8) g v g' ∧ x = BitVec.setWidth 64 v)) :
    ∃ v, GV P ⟨a, 8⟩ v ∧ g.2 < g'.2 ∧ x = BitVec.setWidth 64 v := by
  obtain ⟨v, ⟨hs, ht⟩, rfl⟩ := shared_of_heapOff_load (n := 8) hH ha (by decide) h
  exact ⟨v, hs, by simp only [SharedAccess.tick] at ht; omega, rfl⟩

/-- A combined store at a heap address in `IX P`: `dmem` unchanged, the
counter moved. -/
theorem stI {P : Params} {H : BitVec 64 → Prop} {d m : Mem 64} {a r : BitVec 64} {g g' : (IX P).State}
    (hH : HeapOff H d) (ha : H a)
    (h : ((Mem.loadInt d a 8).isSome = true ∧ m = Mem.storeInt d a 8 r.toInt ∧ g' = g) ∨
      (Mem.loadInt d a 8 = none ∧ m = d ∧ ∃ ok, (IX P).step (.store .plain false a 8 (r.setWidth 128)) g ok g')) :
    m = d ∧ g.2 < g'.2 := by
  obtain ⟨rfl, ok, -, ht⟩ := shared_of_heapOff_store (n := 8) hH ha (by decide) h
  exact ⟨rfl, by simp only [SharedAccess.tick] at ht; omega⟩

/-- `top` is in `SL P`. -/
theorem sl_t (P : Params) : (P.t, 8) ∈ SL P := by simp

/-- A zero displacement. -/
theorem e0 (x : BitVec 64) : x + Int64.toBitVec 0 = x := by simp

/-- The permissions of `IX P`, unfolded. -/
theorem okI {P : Params} {a : SharedAccess} {g : (IX P).State} :
    (IX P).ok a g ↔ (SharedEnv.inv (SL P) (GV P)).ok a () ∧ (SharedEnv.relPureQ Arch.tso fun _ _ => False).ok a () :=
  Iff.rfl

/-- A word read from a `GV P` payload, widened back, is in `GV P`. -/
theorem gv_w {P : Params} {l l' : Loc} {v : Val} (h : GV P l v) : GV P l' (BitVec.setWidth 128 (BitVec.setWidth 64 v)) := by
  rcases h with rfl | rfl | rfl <;> simp [GV]

/-- A node is in `GV P`. -/
theorem gv_n {P : Params} {l : Loc} {w : Nat} (hw : w < 2) : GV P l (BitVec.setWidth 128 (P.n w)) := by
  rcases w with _ | _ | w
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · omega

/-- The value `lock cmpxchgq` writes is its source operand. -/
theorem cas_new {e n : BitVec 64} {old v : BitVec 128}
    (h : rmwOp128 Width.W64 (fun x => if (x == e) = true then some n else none) old = some v) :
    v = BitVec.setWidth 128 n := by
  simp only [rmwOp128] at h
  split at h
  · simp at h; exact h.symm
  · simp at h

/-- `SL P` has no location wider than 16 bytes. -/
theorem le16_SL (P : Params) : Le16 (SL P) := fun x hx => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotX)]

local instance pilotX.envI : CodeEnv := ⟨layout pilotX⟩

/-- `push`'s precondition in `IX P`. -/
def PushPreI (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (_ : (IX P).State) : Prop :=
  t.regs.get64 .rdi = P.t ∧ t.regs.get64 .rsi = P.n w ∧ RetAt t ra ∧ HeapOff (HP P) t.dmem

/-- `push`'s postcondition in `IX P`. -/
def PushPostI (P : Params) (_ : Int64) (t : MachineData) (_ : (IX P).State) (s : MachineData) (_ : (IX P).State) :
    Prop :=
  Saved t s ∧ s.regs.get64 .rsp = t.regs.get64 .rsp + 8

/-- `push`'s loop table in `IX P`. -/
abbrev pushTableI (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (IX P).State) :
    Label → MachineData → (IX P).State → Prop :=
  fun lb s _ => lb = "push" ∧ s.regs.get64 .rdi = P.t ∧ s.regs.get64 .rsi = P.n w ∧ Saved t s ∧
    s.regs.get64 .rsp = t.regs.get64 .rsp

/-- **`push` in `IX P`.** -/
theorem push_specI (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (IX P) ((_root_.Executable.labels cenv).label "push") (PushPreI P w) (PushPostI P) := by
  refine FunSpecPartialEnv.of_cfg (p := pushFragX) (pushTableI P w) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotX_placed (by decide))
    (fun ra t g ⟨h1, h2, _, _⟩ => ⟨rfl, h1, h2, Saved.refl t, rfl⟩) ?_
  rintro ra t g ⟨-, -, ⟨v0, hv0, hra⟩, hH⟩
  cfg_cases_env [pushFragX]
  intro s₀ g₀
  vcgen
  all_goals simp only [okI, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0]
  case vc1 s σ hpre _ =>
    obtain ⟨⟨-, hdi, -⟩, rfl, rfl⟩ := hpre
    rw [hdi]
    exact ⟨sl_t P, trivial⟩
  case vc2 s σ hpre x σ1 hld _ =>
    obtain ⟨⟨-, hdi, hsi, ⟨-, -, -, -, -, -, fdm⟩, -⟩, rfl, rfl⟩ := hpre
    obtain ⟨v, hg, -, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    simp only [hsi]
    exact ⟨⟨sl_n P hw, gv_w hg⟩, fun h => h rfl⟩
  case vc3 s σ hpre v σ1 hld dm σ2 hst =>
    obtain ⟨⟨-, hdi, hsi, ⟨-, -, -, -, -, -, fdm⟩, -⟩, rfl, rfl⟩ := hpre
    obtain ⟨rfl, -⟩ := stI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0, hsi]; exact hp_n P hw) hst
    rw [hdi]
    exact (fdm ▸ hH : HeapOff (HP P) s.dmem).loadInt_none (hp_t P) (by decide)
  case vc4 s σ hpre v σ1 hld dm σ2 hst =>
    obtain ⟨⟨-, hdi, hsi, -⟩, rfl, rfl⟩ := hpre
    rw [hdi]
    exact ⟨⟨sl_t P, fun _ _ v hv => by rw [cas_new hv, hsi]; exact gv_n hw⟩, fun h => absurd rfl h⟩
  case vc5 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas heq hz =>
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc6 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas heq hz hnone =>
    obtain ⟨⟨-, -, hsi, ⟨-, -, -, -, -, -, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨rfl, -⟩ := stI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0, hsi]; exact hp_n P hw) hst
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hnone
    rw [fdm, hsp, hv0] at hnone
    cases hnone
  case vc7 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas heq hz ra σ4 hret =>
    obtain ⟨⟨-, -, hsi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨rfl, -⟩ := stI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0, hsi]; exact hp_n P hw) hst
    obtain ⟨u, hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rw [fdm, hsp, hv0]; rfl)
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hu
    rw [fdm, hsp, hv0] at hu
    cases hu
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc8 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas hne hz =>
    obtain ⟨⟨-, hdi, hsi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨v', -, l1, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    obtain ⟨rfl, l2⟩ := stI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0, hsi]; exact hp_n P hw) hst
    have l3 := hcas.2
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩)
    rotate_left 9
    · subst hg
      simp only [SharedAccess.tick] at l3
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc9 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas hne hz _ =>
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne
  case vc10 s σ hpre v σ1 hld dm σ2 hst old σ3 hcas hne hz _ _ _ =>
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

/-- `pop`'s precondition in `IX P`. -/
def PopPreI (P : Params) (ra : Int64) (t : MachineData) (_ : (IX P).State) : Prop :=
  t.regs.get64 .rdi = P.t ∧ RetAt t ra ∧ HeapOff (HP P) t.dmem

/-- `pop`'s loop table in `IX P`. -/
abbrev popTableI (P : Params) (_ : Int64) (t : MachineData) (_ : (IX P).State) :
    Label → MachineData → (IX P).State → Prop :=
  fun lb s _ => lb = "pop" ∧ s.regs.get64 .rdi = P.t ∧ Saved t s ∧ s.regs.get64 .rsp = t.regs.get64 .rsp

/-- **`pop` in `IX P`** (post: callee-saved registers kept, `rsp` popped). -/
theorem pop_specI (P : Params) :
    FunSpecPartialEnv (IX P) ((_root_.Executable.labels cenv).label "pop") (PopPreI P) (PushPostI P) := by
  refine FunSpecPartialEnv.of_cfg (p := popFragX) (popTableI P) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotX_placed (by decide))
    (fun ra t g ⟨h1, _, _⟩ => ⟨rfl, h1, Saved.refl t, rfl⟩) ?_
  rintro ra t g ⟨-, ⟨v0, hv0, hra⟩, hH⟩
  cfg_cases_env [popFragX]
  intro s₀ g₀
  vcgen
  all_goals simp only [okI, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e0]
  case vc1 s σ hpre _ =>
    obtain ⟨⟨-, hdi, -⟩, rfl, rfl⟩ := hpre
    rw [hdi]
    exact ⟨sl_t P, trivial⟩
  case vc2 s σ hpre v σ1 hld af hz =>
    obtain ⟨⟨-, hdi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨v', -, l1, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩)
    rotate_left 8
    · subst hg
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc3 s σ hpre v σ1 hld af hz _ =>
    obtain ⟨⟨-, hdi, ⟨-, -, -, -, -, -, fdm⟩, -⟩, rfl, rfl⟩ := hpre
    obtain ⟨v', hg, -, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    have hz' : BitVec.setWidth 64 v' ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    rw [hn']
    exact ⟨sl_n P hw', trivial⟩
  case vc4 s σ hpre v σ1 hld af hz u σ2 hld2 =>
    obtain ⟨⟨-, hdi, ⟨-, -, -, -, -, -, fdm⟩, -⟩, rfl, rfl⟩ := hpre
    rw [hdi]
    exact (fdm ▸ hH : HeapOff (HP P) s.dmem).loadInt_none (hp_t P) (by decide)
  case vc5 s σ hpre v σ1 hld af hz u σ2 hld2 =>
    obtain ⟨⟨-, hdi, ⟨-, -, -, -, -, -, fdm⟩, -⟩, rfl, rfl⟩ := hpre
    obtain ⟨v', hg, -, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    have hz' : BitVec.setWidth 64 v' ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u', hu, -, rfl⟩ := ldI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, ↓reduceIte, e0, hn']; exact hp_n P hw') hld2
    rw [hdi]
    exact ⟨⟨sl_t P, fun _ _ v hv => by rw [cas_new hv]; exact gv_w hu⟩, fun h => absurd rfl h⟩
  case vc6 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas heq hz2 =>
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz2
  case vc7 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas heq hz2 hnone =>
    obtain ⟨⟨-, -, ⟨-, -, -, -, -, -, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hnone
    rw [fdm, hsp, hv0] at hnone
    cases hnone
  case vc8 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas heq hz2 ra σ4 hret =>
    obtain ⟨⟨-, -, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨u, hu, rfl, rfl⟩ := private_of_mapped_load (hc := hret) (by
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rw [fdm, hsp, hv0]; rfl)
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hu
    rw [fdm, hsp, hv0] at hu
    cases hu
    refine .inr ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc9 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas hne hz2 =>
    obtain ⟨⟨-, hdi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hsp⟩, rfl, rfl⟩ := hpre
    obtain ⟨v', hg, l1, rfl⟩ := ldI (fdm ▸ hH) (by simp only [e0, hdi]; exact hp_t P) hld
    have hz' : BitVec.setWidth 64 v' ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    obtain ⟨w', hw', hn'⟩ := gv_node hg hz'
    obtain ⟨u', -, l2, rfl⟩ := ldI (fdm ▸ hH) (by simp only [Reg64s.get64_set64, ↓reduceIte, e0, hn']; exact hp_n P hw') hld2
    have l3 := hcas.2
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩,
      .inr fun ⟨_, hg'⟩ => ?_⟩)
    rotate_left 8
    · subst hg'
      simp only [SharedAccess.tick] at l3
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals first | assumption | (rw [hsp]; rfl) | rw [hsp]
  case vc10 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas hne hz2 _ =>
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne
  case vc11 s σ hpre v σ1 hld af hz u σ2 hld2 old σ3 hcas hne hz2 _ _ _ =>
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz2).symm hne
      | exact absurd hz2.symm hne
      | exact absurd hz2 hne

/-! ## `main` -/

/-- `main`'s precondition in `IX P` (`MainPre` without the ownership facts). -/
def MainPreI (P : Params) (w : Nat) (raM : Int64) (s : MachineData) (_ : (IX P).State) : Prop :=
  s.regs.get64 .rbx = P.t ∧ s.regs.get64 .r14 = P.n w ∧ s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 ∧
    RetAt s raM ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - 16) 8).isSome = true ∧ HeapOff (HP P) s.dmem

/-- **`main` in `IX P`**: no error, and at the end the return address is
`raM`. -/
theorem main_specI (P : Params) (w : Nat) (hw : w < 2) (raM : Int64) :
    PartialTripleEnv (IX P) (MainPreI P w raM) pilotX (fun _ _ => False) (fun a _ _ => a = raM) := by
  rw [pilotX_split]
  refine PartialTripleEnv.of_partialWpEnv fun s g ⟨hbx, h14, h15, ⟨v0, hv0, hra⟩, hsl, hH⟩ => ?_
  refine PartialWpEnv.append_false ?_
  refine PartialWpEnv.seg (R := fun s₁ => s₁.regs.get64 .rsp = s.regs.get64 .rsp - 8 ∧
      s₁.regs.get64 .rsi = P.n w ∧ s₁.regs.get64 .rdi = P.t ∧ s₁.regs.get64 .rbx = P.t ∧ s₁.dmem = s.dmem)
    (X := fun _ _ => False) ?_ ?_ (fun _ _ _ h _ => h.elim)
  · simp only [mainA]
    vcgen
    case vc1 s' hs hz =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hz
      have e16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16 := by decide
      rw [e16, BitVec.add_comm, ja_not_taken h15] at hz
      exact Bool.false_ne_true hz
    case vc2 s' hs hz =>
      subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14, and_true]
      rfl
  rintro s₁ g₁ ⟨h1sp, h1si, h1di, h1bx, h1dm⟩ -
  have e8 : s₁.regs.get64 .rsp - Width.W64.bytesv = s.regs.get64 .rsp - 16 := by
    rw [h1sp, show Width.W64.bytesv = (8 : BitVec 64) from rfl]; bv_omega
  have hsl₁ : (Mem.loadInt s₁.dmem (s₁.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
    rw [e8, h1dm]; exact hsl
  have h_rt : ∀ (m : DataMem) (a : BitVec 64) (x : Int),
      Mem.loadInt (Mem.storeInt m a 8 x) a 8 = some (Int.ofBytes (Int.toBytes 8 x)) :=
    fun m a x => Mem.loadInt_storeInt m a 8 x (by decide)
  refine PartialWpEnv.call _ _ "push" (push_specI P w hw) hsl₁ fun ra => ⟨?_, fun s₂ g₂ hpo => ?_⟩
  · refine ⟨by simpa using h1di, by simpa using h1si, ⟨_, by simpa using h_rt _ _ _, ?_⟩,
      (h1dm ▸ hH : HeapOff (HP P) s₁.dmem).storeInt hsl₁ _⟩
    simpa using Int64.ofBitVec_ofBytes_toBytes ra
  · obtain ⟨⟨h2bx, -, -, -, -, -, h2dm⟩, h2sp⟩ := hpo
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at h2bx h2sp h2dm
    show PartialWpEnv _ (mainB ++ (callPop ++ mainC)) _ _ _ _
    refine PartialWpEnv.seg (R := fun s₃ => s₃.regs.get64 .rdi = P.t ∧ s₃.regs.get64 .rsp = s₂.regs.get64 .rsp ∧
        s₃.dmem = s₂.dmem) (X := fun _ _ => False) ?_ ?_ (fun _ _ _ h _ => h.elim)
    · simp only [mainB]
      vcgen
      case vc1 s' hs =>
        subst hs
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h2bx, h1bx, and_true]
    rintro s₃ g₃ ⟨h3di, h3sp, h3dm⟩ -
    have e3 : s₃.regs.get64 .rsp - Width.W64.bytesv = s₁.regs.get64 .rsp - Width.W64.bytesv := by
      rw [h3sp, h2sp, show Width.W64.bytesv = (8 : BitVec 64) from rfl]; bv_omega
    have hsl₃ : (Mem.loadInt s₃.dmem (s₃.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e3, h3dm, h2dm]; exact isSome_loadInt_storeInt hsl₁ _ _ _
    have hH₃ : HeapOff (HP P) s₃.dmem := by
      rw [h3dm, h2dm]; exact (h1dm ▸ hH : HeapOff (HP P) s₁.dmem).storeInt hsl₁ _
    refine PartialWpEnv.call _ _ "pop" (pop_specI P) hsl₃ fun ra' => ⟨?_, fun s₄ g₄ hpo' => ?_⟩
    · refine ⟨by simpa using h3di, ⟨_, by simpa using h_rt _ _ _, ?_⟩, hH₃.storeInt hsl₃ _⟩
      simpa using Int64.ofBitVec_ofBytes_toBytes ra'
    obtain ⟨⟨-, -, -, -, -, -, h4dm⟩, h4sp⟩ := hpo'
    simp only [Reg64s.get64_set64, ↓reduceIte] at h4sp h4dm
    have e4 : 8 + s₄.regs.get64 .rsp = s.regs.get64 .rsp := by
      rw [h4sp, h3sp, h2sp, h1sp]; bv_omega
    have hab : ∀ m (v : Int), Mem.loadInt (Mem.storeInt m (s.regs.get64 .rsp - 16) 8 v) (s.regs.get64 .rsp) 8 =
        Mem.loadInt m (s.regs.get64 .rsp) 8 := fun m v =>
      Mem.loadInt_storeInt_of_above _ _ _ 8 8 _ (by simp; bv_omega) (by simp; bv_omega)
    have hret : Mem.loadInt s₄.dmem (8 + s₄.regs.get64 .rsp) 8 = some v0 := by
      rw [e4, h4dm, h3dm, h2dm, show s₃.regs.get64 .rsp - BitVec.ofNat 64 8 = s.regs.get64 .rsp - 16 from e3.trans e8,
        show s₁.regs.get64 .rsp - Width.W64.bytesv = s.regs.get64 .rsp - 16 from e8, hab, hab, h1dm, hv0]
    show PartialWpEnv _ (mainC ++ []) _ _ _ _
    refine PartialWpEnv.seg (R := fun _ => False) (X := fun a _ => a = raM) ?_ (fun _ _ h _ => h.elim) ?_
    · simp only [mainC]
      vcgen
      case vc1 s' hs =>
        subst hs
        simp only [MachineData.retAddr, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
          show BitVec.setWidth 64 (Int64.toBitVec 8) = 8 from rfl, show Width.W64.bytes = 8 from rfl, hret,
          Option.map_some, Option.isSome_some]
      case vc2 s' hs a ha =>
        subst hs
        simp only [MachineData.retAddr, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
          show BitVec.setWidth 64 (Int64.toBitVec 8) = 8 from rfl, show Width.W64.bytes = 8 from rfl, hret,
          Option.map_some, Option.some.injEq] at ha ⊢
        exact ha ▸ hra
    exact fun _ _ _ h _ => h

/-! ## The purity specification -/

/-- **`pilotX`'s purity specification** in `relInvX (SL P) (GV P)`: the text,
to its end. -/
def pilotXPure (P : Params) : RelPureSpecQX Arch.tso fun _ _ => False where
  S := SL P
  le16 := le16_SL P
  e := layout pilotX
  valid := inferInstance
  endPc := endPX
  post y := y.1.2 = endPX
  post_end _ h := h

/-- **The purity specification holds at thread `w`'s start** (`main_specI`,
uncounted). -/
theorem pilotXPure_holds (P : Params) {w : Nat} (hw : w < 2) {s : isa.State} (hS : StartPX P w s) :
    (pilotXPure P).HoldsV (GV P) s := by
  refine ⟨hS.exe, hS.endPc, hS.decls, hS.heap, ?_⟩
  have hst : s.st = (s.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hS.pc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  refine (Program.instrStepEnv_of_partialTripleEnv (main_specI P w hw endPX) (g := ((), 0))
    ⟨hS.rbx, hS.r14, hS.r15, hS.ret, hS.slot, hS.heap⟩).uncountEnv.mono ?_
  intro _ hy
  obtain ⟨_, ⟨-, h⟩ | h⟩ := hy
  · exact h.elim
  · exact h

end Kraken.Promising.Lower.PilotX

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X

/-! ## The whole program -/

/-- The two threads' layouts as one family. -/
abbrev layouts (l0 l1 : _root_.Layout) : Nat → _root_.Layout
  | 0 => l0
  | _ + 1 => l1

/-- **The x64 Treiber pilot with a `dmem` call stack, on the Promising model**
(`Arch.tso`, executable machine): every final configuration reachable from
two threads at their starts (`StartPX`, thread `w` at its own layout) has
each thread popped one of the two nodes, the two distinct. Start facts only:
`top` is initially `0` and the initial memory satisfies the value invariant
`GV P` (`hm0`). The bridge is `Vals.envGValsBridgeX_ofPure` with the purity
specification `pilotXPure` (judgment in `relInvX`). -/
theorem pilotX_promising {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 pilotX)] [Executable.ValidLayout (l1 pilotX)] {P : Params} (hL : TLocs P)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartPX (layout := l0) P 0 s0) (h1 : StartPX (layout := l1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    (hm0 : MemInv (GV P) (Config.init [s0, s1] initMem).mem)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg := by
  have hv : ∀ w, Executable.ValidLayout (layouts l0 l1 w pilotX) := fun w => by
    rcases w with _ | _ <;> assumption
  refine Vals.envGValsBridgeX_ofPure (le16_SL P) (GV P) (erase_init hL _) (ghost₀_pend _)
    (fun w => pilotXPure (layout := layouts l0 l1 w) P) (fun w => @pilotX_phase1FX (layouts l0 l1 w) (hv w))
    ?_ hm0 (hthr_pX (layouts l0 l1) hL h0 h1 hT0) hc hf
    fun _ _ E' hle hsize hB => pilotX_final hL hf E' hle hsize hB
  rintro (_ | _ | w) s hs
  · cases hs; exact pilotXPure_holds (layout := l0) P (by decide) h0
  · cases hs; exact pilotXPure_holds (layout := l1) P (by decide) h1
  · cases hs

end Kraken.Promising.Lower.PilotX

#print axioms Kraken.Promising.Lower.PilotX.pilotX_promising
