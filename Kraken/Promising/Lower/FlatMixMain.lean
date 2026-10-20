/-
A thread that looks a key up in its private FlatHashMap and enqueues the
answer into the shared Michael–Scott queue: `main`'s fragment specification.
ISA: AArch64.

`mixMain` (`main`) saves the link and calls `flat_lookup` (the lowered
FlatHashMap `lookup`, on a table in the thread's `dmem`). It then writes the
answer into the first node's data word (the value on a hit, the marker `1` on
a miss, selected by `cmp`/`csel`) and enqueues that node with `enq`. Then it
writes `2` into the second node's data word, enqueues that node, and returns.
The queue arguments arrive in callee-saved registers: `q = &head` in `x25`
and the nodes in `x26`/`x27`. The stored value stays in `x20`.

* `FragSpecEnvL.ofProcSpecLe`: the lifting of a placement-independent
  sequential `ProcSpec` (`FragSpecEnvL.ofProcSpec`) in a fence-monotone
  environment, keeping `FenceMono.le` of the environment state. The caller's
  protocol facts (`Start`, which is fence-stable) survive the call.
* `mixMain_fragL`: `main`'s `FragSpecEnvL` over `[mixMain, flatLookup,
  enqFrag]` in msqueue2's value-restricted enqueuer environment
  `counted (EQG P G)` (`Lower/MsqPilotEnqFrame.lean`), from `lookup_spec` (lifted)
  and `enqFrag_specF` (twice). The frame is the private memory `d₀` with
  `F d₀`, under `QFrameOK P G F` and with both data words unmapped.
  **Hypothesis (`Low1`)**: msqueue2's protocol pins the first node's data
  word to low 32 bits `1` (`MsQueue.D`), so the theorem assumes that the
  lookup's answer, if a hit, has low 32 bits `1`. The marker is `1`. The post
  records the stored value (`x20 = Stored r` for the lookup's answer `r`),
  `ComE2` and the unchanged `dmem`.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.Promising.Lower.MsqPilotEnqFrame
import Kraken.Promising.Lower.FlatWholeSpec
import Kraken.Promising.Lower.FragSpecProc

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.AArch64.Parser

namespace Kraken.Promising.Lower.Flat.Mix

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved)
open Kraken.Promising.Lower.MsqPilot (enqFrag blTo EQG QFrameOK enqFrag_specF)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The lifting, keeping the fence order

The generic form is `MachineWP.FragSpecEnvL.ofProcSpecLe`
(`Lower/FragSpecProc.lean`); the name below is kept as an alias. -/

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every fence-monotone environment**, with the environment state moved only by
fences (`FenceMono.le`). -/
theorem FragSpecEnvL.ofProcSpecLe {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) [env.FenceMono] (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t)
      (fun ra t g t' g' => Post x ra t t' ∧ SharedEnv.FenceMono.le g g') :=
  MachineWP.FragSpecEnvL.ofProcSpecLe h env x

/-! ## The text -/

/-- `main`: save the link, `lookup`, select the stored value, write the first
data word, `enq`, write the second, `enq`, return. One block. -/
def mixMain : Program := parseAArch64("
main:
    mov x19, x30
    bl flat_lookup
    mov x9, #1
    cmp x0, #0
    csel x20, x1, x9, ne
    str w20, [x26]
    mov x0, x25
    mov x1, x26
    bl enq
    mov w9, #2
    str w9, [x27]
    mov x0, x25
    mov x1, x27
    bl enq
    mov x30, x19
    ret
")

def mPre : Program := parseAArch64("
    mov x19, x30
")
def mMid1 : Program := parseAArch64("
    mov x9, #1
    cmp x0, #0
    csel x20, x1, x9, ne
    str w20, [x26]
    mov x0, x25
    mov x1, x26
")
def mMid2 : Program := parseAArch64("
    mov w9, #2
    str w9, [x27]
    mov x0, x25
    mov x1, x27
")
def mTail : Program := parseAArch64("
    mov x30, x19
    ret
")
/-- `main`'s block, cut at its calls. -/
def mixBody : Program :=
  mPre ++ blTo "flat_lookup" :: (mMid1 ++ blTo "enq" :: (mMid2 ++ blTo "enq" :: (mTail ++ [])))

theorem mixMain_block : Program.blockAt mixMain "main" = some ⟨"main", mixBody, none⟩ := by decide

/-! ## The predicates -/

/-- **The hit-or-marker hypothesis**: a hit's value has low 32 bits `1`
(msqueue2's data word property `MsQueue.D`). -/
def Low1 : Option Nat → Prop
  | none => True
  | some y => y % 2 ^ 32 = 1

/-- The value `main` stores: the hit's value, or the marker `1`. -/
def Stored : Option Nat → Nat
  | none => 1
  | some y => y

/-- `main`'s precondition: `lookup`'s at the link `ra`, the queue arguments,
the private memory `d₀`, the hypothesis `Low1`, and phase 1's `Start`. -/
def MixPre (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EQG P G)).State) : Prop :=
  LookupPre x ra t ∧ t.regs.X25.toBitVec = P.h ∧ t.regs.X26.toBitVec = P.n1 ∧ t.regs.X27.toBitVec = P.n2 ∧
    t.dmem = d₀ ∧ (∀ r, lookupN x.1 x.2 = some r → Low1 r) ∧ Start P (ph1 P) σ.1

/-- The stored value in `x20`, for the lookup's answer. -/
def StoredIn (x : Tbl × Nat) (s : MachineData) : Prop :=
  ∃ r, lookupN x.1 x.2 = some r ∧ s.regs.X20.toNat = Stored r

/-- `main`'s postcondition: `ComE2`, the stored value, `dmem` unchanged. -/
def MixPost (P : Params2) (G : Loc → Val → Prop) (x : Tbl × Nat) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EQG P G)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EQG P G)).State) :
    Prop :=
  ComE2 P σ'.1 ∧ StoredIn x t' ∧ t'.dmem = t.dmem

/-- What every piece keeps: the saved link, the queue arguments, `dmem`. -/
def Keep (P : Params2) (ra : Int64) (d₀ : Mem 64) (s : MachineData) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X25.toBitVec = P.h ∧ s.regs.X26.toBitVec = P.n1 ∧
    s.regs.X27.toBitVec = P.n2 ∧ s.dmem = d₀

/-- Behind `bl flat_lookup`: the answer `r` in `x0`/`x1`, `Low1 r`. -/
def AfterLookup (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) (s : MachineData)
    (σ : (SharedEnv.counted (EQG P G)).State) : Prop :=
  (∃ r, lookupN x.1 x.2 = some r ∧ ResRegs r s ∧ Low1 r) ∧ Keep P ra d₀ s ∧ Start P (ph1 P) σ.1

/-- At a `bl enq` of phase `ph`. -/
def AtEnqM (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) (ph : Ph)
    (s : MachineData) (σ : (SharedEnv.counted (EQG P G)).State) : Prop :=
  s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = ph.n ∧ Keep P ra d₀ s ∧ StoredIn x s ∧ EL' P ph σ.1

/-- Behind a `bl enq` of phase `ph`. -/
def AfterEnqM (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) (ph : Ph)
    (s : MachineData) (σ : (SharedEnv.counted (EQG P G)).State) : Prop :=
  Keep P ra d₀ s ∧ StoredIn x s ∧ Linked P ph σ.1

/-! ## The straight-line pieces -/

section Pieces
variable [CodeEnv]

theorem mix_pre (P : Params2) (hL : QLocs2 P) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => MixPre P G d₀ x ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mPre⟩ : EnvProgram (SharedEnv.counted (EQG P G)))
    ⦃ (fun _ s σ => MixPre P G d₀ x ra s σ ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mPre
  vcgen
  rename_i s σ0 hpre σ1 hf
  obtain ⟨⟨⟨⟨h0, h1, h2, h3, h4, h30⟩, hm, hb, hpe⟩, h25, h26, h27, hd, hlo, hS⟩, rfl, rfl⟩ := hpre
  subst hd
  simp [MixPre, LookupPre, Args, h0, h1, h2, h3, h4, h30, h25, h26, h27, hm, hb, hpe]
  exact ⟨hlo, hS.fence (ph1_ok hL) hf.1⟩

theorem mix_mid1 (P : Params2) (hL : QLocs2 P) (G : Loc → Val → Prop) (d₀ : Mem 64)
    (hd : Mem.loadInt d₀ P.n1 4 = none) (x : Tbl × Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterLookup P G d₀ x ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mMid1⟩ : EnvProgram (SharedEnv.counted (EQG P G)))
    ⦃ (fun _ s σ => AtEnqM P G d₀ x ra (ph1 P) s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mMid1
  vcgen
  case vc2 =>
    rename_i s σ0 hpre σ1 hf1 rng σ2 hf2 σ3 hf3 rng2 hnone
    simp only [SharedEnv.counted_ok]
    obtain ⟨⟨⟨r, hr, hres, hlo⟩, ⟨h19, h25, h26, h27, hd0⟩, hS⟩, rfl, rfl⟩ := hpre
    have hE := ((hS.fence (ph1_ok hL) hf1.1).fence (ph1_ok hL) hf2.1).fence (ph1_ok hL) hf3.1
    rcases r with _ | y <;> simp only [ResRegs, Low1] at hres hlo
    · simp [hres, h26]
      simpa [ph1, Params.dat] using (vc_e_str2 (ph1_ok hL) _ hE (1#128) (by simp [ph1, D])).1
    · obtain ⟨hx0, hx1⟩ := hres
      simp [hx0, h26]
      have hv : D (BitVec.setWidth 128 (BitVec.setWidth 32 s.regs.X1.toBitVec)) := by
        simp only [D]
        apply BitVec.eq_of_toNat_eq
        simp [hx1, hlo]
      simpa [ph1, Params.dat] using (vc_e_str2 (ph1_ok hL) _ hE _ hv).1
  case vc3 =>
    rename_i s σ0 hpre σ1 hf1 rng σ2 hf2 σ3 hf3 rng2 dm σ4 hst σ5 hf4 σ6 hf5
    obtain ⟨⟨⟨r, hr, hres, hlo⟩, ⟨h19, h25, h26, h27, hd0⟩, hS⟩, rfl, rfl⟩ := hpre
    have hE := ((hS.fence (ph1_ok hL) hf1.1).fence (ph1_ok hL) hf2.1).fence (ph1_ok hL) hf3.1
    subst hd0
    rcases r with _ | y <;> simp only [ResRegs, Low1] at hres hlo
    · simp [hres, h26, hd] at hst
      obtain ⟨rfl, hso⟩ := hst
      have hE' : EL' P (ph1 P) σ4.1 := by
        rcases hso with h | h <;> exact (vc_e_str2 (ph1_ok hL) _ hE (1#128) (by simp [ph1, D])).2 _ σ4.1
          (by simpa [ph1, Params.dat, h26, hres] using h.1)
      refine ⟨by simp [h25], by simp [ph1, h26], ⟨by simpa using h19, by simp [h25], by simp [h26], by simp [h27], rfl⟩,
        ⟨_, hr, by simp [hres, Stored]; rfl⟩, (hE'.fence (ph1_ok hL) hf4.1).fence (ph1_ok hL) hf5.1⟩
    · obtain ⟨hx0, hx1⟩ := hres
      simp [hx0, h26, hd] at hst
      obtain ⟨rfl, hso⟩ := hst
      have hv : D (BitVec.setWidth 128 (BitVec.setWidth 32 s.regs.X1.toBitVec)) := by
        simp only [D]
        apply BitVec.eq_of_toNat_eq
        simp [hx1, hlo]
      have hE' : EL' P (ph1 P) σ4.1 := by
        rcases hso with h | h <;> exact (vc_e_str2 (ph1_ok hL) _ hE _ hv).2 _ σ4.1
          (by simpa [ph1, Params.dat, h26, hx0] using h.1)
      refine ⟨by simp [h25], by simp [ph1, h26], ⟨by simpa using h19, by simp [h25], by simp [h26], by simp [h27], rfl⟩,
        ⟨_, hr, by simp [hx0, hx1, Stored]⟩, (hE'.fence (ph1_ok hL) hf4.1).fence (ph1_ok hL) hf5.1⟩
  all_goals simp

theorem mix_mid2 (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (hd : Mem.loadInt d₀ P.n2 4 = none)
    (x : Tbl × Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnqM P G d₀ x ra (ph1 P) s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mMid2⟩ : EnvProgram (SharedEnv.counted (EQG P G)))
    ⦃ (fun _ s σ => AtEnqM P G d₀ x ra (ph2 P) s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mMid2
  vcgen
  case vc2 =>
    rename_i s σ0 hpre σ1 hf1 rng hnone
    simp only [SharedEnv.counted_ok]
    obtain ⟨⟨⟨h19, h25, h26, h27, hd0⟩, hR, hT⟩, rfl, rfl⟩ := hpre
    have hE : Start P (ph2 P) σ1.1 := Start.fence (ph2_ok P) hT hf1.1
    simp [h27]
    simpa [ph2, Params2.dat2] using (vc_e_str2 (ph2_ok P) _ hE (2#128) (by simp [ph2, D2])).1
  case vc3 =>
    rename_i s σ0 hpre σ1 hf1 rng dm σ2 hst σ3 hf2 σ4 hf3
    obtain ⟨⟨⟨h19, h25, h26, h27, hd0⟩, ⟨r, hr, hx20⟩, hT⟩, rfl, rfl⟩ := hpre
    have hE : Start P (ph2 P) σ1.1 := Start.fence (ph2_ok P) hT hf1.1
    subst hd0
    simp [h27, hd] at hst
    obtain ⟨rfl, hso⟩ := hst
    have hE' : EL' P (ph2 P) σ2.1 := by
      rcases hso with h | h <;> exact (vc_e_str2 (ph2_ok P) _ hE (2#128) (by simp [ph2, D2])).2 _ σ2.1
        (by simpa [ph2, Params2.dat2, h27] using h.1)
    exact ⟨by simp [h25], by simp [ph2, h27], ⟨by simpa using h19, by simp [h25], by simp [h26], by simp [h27], rfl⟩,
      ⟨r, hr, by simpa using hx20⟩, (hE'.fence (ph2_ok P) hf2.1).fence (ph2_ok P) hf3.1⟩
  all_goals simp

theorem mix_tail (P : Params2) (G : Loc → Val → Prop) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => AfterEnqM P G d₀ x ra (ph2 P) s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mTail⟩ : EnvProgram (SharedEnv.counted (EQG P G)))
    ⦃ (fun _ _ _ => False); fun a s σ => a = ra ∧ ComE2 P σ.1 ∧ StoredIn x s ∧ s.dmem = d₀ ⦄ := by
  intro s₀ g₀
  unfold mTail
  vcgen
  rename_i s σ0 hpre σ1 hf1 σ2 hf2
  obtain ⟨⟨⟨h19, h25, h26, h27, hd0⟩, ⟨r, hr, hx20⟩, hT⟩, rfl, rfl⟩ := hpre
  exact ⟨by simpa using h19, ((hT.fence (ph2_ok P) hf1.1).fence (ph2_ok P) hf2.1).1, ⟨r, hr, by simpa using hx20⟩,
    by simpa using hd0⟩

end Pieces

/-! ## `main` -/

/-- `Keep` and the stored value survive a call whose callee keeps
`CalleeSaved`. -/
theorem keep_of_calleeSaved {P : Params2} {ra ra' : Int64} {d₀ : Mem 64} {x : Tbl × Nat} {s s' : MachineData}
    (hk : Keep P ra d₀ s) (hs : StoredIn x s) (hc : CalleeSaved (s.setLr ra') s') : Keep P ra d₀ s' ∧ StoredIn x s' := by
  obtain ⟨h19, h25, h26, h27, hd⟩ := hk
  obtain ⟨r, hr, h20⟩ := hs
  obtain ⟨c19, c20, -, -, -, -, c25, c26, c27, -, cd⟩ := hc
  simp only [MachineData.setLr, Reg64s.setXReg] at c19 c20 c25 c26 c27 cd
  exact ⟨⟨by rw [c19]; exact h19, by rw [c25]; exact h25, by rw [c26]; exact h26, by rw [c27]; exact h27,
    by rw [cd]; exact hd⟩, r, hr, by rw [c20]; exact h20⟩

/-- **`main`'s specification**: in every code placing `main`, `flat_lookup`
and `enq`, entered with `lookup`'s precondition, the queue arguments, the
private memory `d₀` (with `F d₀`, `QFrameOK P G F` and both data words
unmapped), the hypothesis `Low1` and phase 1's `Start`, every run returns to
`ra` with `ComE2`, the stored value `Stored r` for the lookup's answer `r` in
`x20`, and `dmem` unchanged. -/
theorem mixMain_fragL (P : Params2) (hL : QLocs2 P) (ht : P.t = P.h + 8) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : QFrameOK P G F) (d₀ : Mem 64) (hd₀ : F d₀) (hn1 : Mem.loadInt d₀ P.n1 4 = none)
    (hn2 : Mem.loadInt d₀ P.n2 4 = none) (x : Tbl × Nat) :
    FragSpecEnvL (SharedEnv.counted (EQG P G)) [mixMain, flatLookup, enqFrag] "main"
      (MixPre P G d₀ x) (MixPost P G x) := by
  refine FragSpecEnvL.of_block mixMain_block fun hpl ra t g hpre => ?_
  have hLk := (FragSpecEnvL.ofProcSpecLe (frags := [flatLookup]) (fun hpl' => lookup_spec (hpl' _ (by simp)))
    (SharedEnv.counted (EQG P G)) x).at_sub hpl (by simp)
  have hE1 := (enqFrag_specF P hL ht (ph1 P) (ph1_ok hL) G F hF).toL.at_sub hpl (by simp)
  have hE2 := (enqFrag_specF P hL ht (ph2 P) (ph2_ok P) G F hF).toL.at_sub hpl (by simp)
  have ht0 : t.dmem = d₀ := hpre.2.2.2.2.1
  have w1 := (mix_pre P hL G d₀ x ra t g).le_wp t g ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at w1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w1)
  rintro s1 σ1 ⟨⟨⟨⟨h0, h1, h2, h3, h4, -⟩, hm, hb, hpe⟩, h25, h26, h27, hd, hlo, hS⟩, h19⟩
  refine PartialWpEnv.call hLk fun ra' => ⟨?_, fun s2 σ2 ⟨hpost, hle⟩ => ?_⟩
  · subst hd
    exact ⟨⟨by simpa [MachineData.setLr, Reg64s.setXReg] using h0, by simpa [MachineData.setLr, Reg64s.setXReg] using h1,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h2, by simpa [MachineData.setLr, Reg64s.setXReg] using h3,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h4, by simp [MachineData.setLr, Reg64s.setXReg]⟩,
      by simpa [MachineData.setLr] using hm, hb, hpe⟩
  obtain ⟨r, hr, hres, hdm, hcs⟩ := hpost
  simp only [Callee, MachineData.setLr, Reg64s.setXReg] at hcs hdm
  obtain ⟨-, c19, -, -, -, -, -, c25, c26, c27, -⟩ := hcs
  have w2 := (mix_mid1 P hL G d₀ (hd ▸ hn1) x ra s2 σ2).le_wp s2 σ2
    ⟨⟨⟨r, hr, hres, hlo r hr⟩, ⟨by rw [c19]; exact h19, by rw [c25]; exact h25, by rw [c26]; exact h26,
      by rw [c27]; exact h27, by rw [hdm]; exact hd⟩, hS.fence (ph1_ok hL) hle.1⟩, rfl, rfl⟩
  rw [wpEnv_eq] at w2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w2)
  rintro s3 σ3 ⟨hx0, hx1, hk3, hs3, hEL⟩
  refine PartialWpEnv.call hE1 fun ra'' => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
    by simpa [MachineData.setLr, Reg64s.setXReg] using hx0, by simpa [MachineData.setLr, Reg64s.setXReg] using hx1,
    by simpa [MachineData.setLr, hk3.2.2.2.2] using hd₀, hEL⟩, fun s4 σ4 ⟨hc4, hLk4⟩ => ?_⟩
  obtain ⟨hk4, hs4⟩ := keep_of_calleeSaved hk3 hs3 hc4
  have w3 := (mix_mid2 P G d₀ hn2 x ra s4 σ4).le_wp s4 σ4 ⟨⟨hk4, hs4, hLk4⟩, rfl, rfl⟩
  rw [wpEnv_eq] at w3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w3)
  rintro s5 σ5 ⟨hx0', hx1', hk5, hs5, hEL'⟩
  refine PartialWpEnv.call hE2 fun ra3 => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
    by simpa [MachineData.setLr, Reg64s.setXReg] using hx0', by simpa [MachineData.setLr, Reg64s.setXReg] using hx1',
    by simpa [MachineData.setLr, hk5.2.2.2.2] using hd₀, hEL'⟩, fun s6 σ6 ⟨hc6, hLk6⟩ => ?_⟩
  obtain ⟨hk6, hs6⟩ := keep_of_calleeSaved hk5 hs5 hc6
  have w4 := (mix_tail P G d₀ x ra s6 σ6).le_wp s6 σ6 ⟨⟨hk6, hs6, hLk6⟩, rfl, rfl⟩
  rw [wpEnv_eq] at w4
  exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim)
    (fun a s σ ⟨hra, hC, hS', hd'⟩ => ⟨hra, hC, hS', by rw [hd', ht0]⟩) w4)

end Kraken.Promising.Lower.Flat.Mix
