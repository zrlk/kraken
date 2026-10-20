/-
The FlatHashMap-lookup → Michael–Scott-queue program, AArch64: value and
purity triples for the value-restricted lowering kit.

`Lower/KitVals.lean`'s `LowerThreadW` asks, per thread, for a value triple in
`counted (inv S G)` (every shared write keeps `G`, every access is an
`S`-location) and a purity triple in `counted (valsEnv (relPure …) G)`. This
file gives them for the two threads of the program of
`Lower/FlatMixMain.lean` (thread `0`: `main` calling the private
FlatHashMap `lookup` and the queue's `enq` twice) and of the MS queue pilot's
dequeuer (thread `1`: `progD`).

* The invariant is msqueue's (`MemValsA64MsQueue`): `QG P` (`head`, `tail`,
  the null node's link and every node's link hold `0` or a node), `QS P` (the
  queue words and every node's data word and link).
* `QPriv P m`: the private memory `m` maps neither `tail`, nor the data words,
  nor any link; it gives `enq`'s frame `QFrameOK P (QG P) (· = m)`
  (`qFrameOK_priv`).
* `enqFrag_valF`: `enq` in `counted (inv (QS P) (QG P))` with a private frame.
* `mixMain_fragG`: **`main`'s fragment spec in every environment `E` whose
  fences skip**, from a spec of `enq` in `counted E` and permission of the
  two 4-byte data stores. The lookup is lifted by `FragSpecEnvL.ofProcSpec`.
  The value and the purity triple of thread `0` are both instances.
* `deq_valQ`, `mainD_valQ`: `progD` in `counted (inv (QS P) (QG P))`, from
  an empty `dmem`.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.Promising.Lower.FlatMixMain
import Kraken.Promising.Lower.MsqPilotPure
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Flat.Mix

open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem)
open Kraken.Promising.Lower.MsqPilot (enqFrag blTo progD deqFrag mainDBody dPre dMid dTail endD
  progD_placed cfgEnv_partial_fun_rank QFrameOK)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The invariant and the private frame -/

/-- The value invariant at `P`: queue words and links hold `0` or a node. -/
abbrev QG (P : Params2) : Loc → Val → Prop := msqGA P.h P.t P.d P.n1 P.n2
/-- The shared locations at `P`. -/
abbrev QS (P : Params2) : SharedEnv.Layout := msqSA P.h P.t P.d P.n1 P.n2
/-- The value environment at `P`. -/
abbrev IVQ (P : Params2) : SharedEnv := SharedEnv.counted (SharedEnv.inv (QS P) (QG P))

/-- A value of a queue word: `0` or a node. -/
def QV (P : Params2) (x : BitVec 64) : Prop := x = 0 ∨ MsqNodeA P.d P.n1 P.n2 x

/-- **The private memory misses the queue**: no 8-byte word at `tail` or at
a link (of the null node or a node), no 4-byte word at the enqueued data. -/
def QPriv (P : Params2) (m : Mem 64) : Prop :=
  Mem.loadInt m P.t 8 = none ∧ Mem.loadInt m 8 8 = none ∧ Mem.loadInt m (P.d + 8) 8 = none ∧
    Mem.loadInt m (P.n1 + 8) 8 = none ∧ Mem.loadInt m (P.n2 + 8) 8 = none ∧ Mem.loadInt m P.n1 4 = none ∧
    Mem.loadInt m P.n2 4 = none

theorem qFrameOK_priv (P : Params2) (m : Mem 64) (h : QPriv P m) : QFrameOK P (QG P) (· = m) := by
  rintro d rfl
  obtain ⟨ht, h8, hd, h1, h2, -, -⟩ := h
  refine ⟨ht, fun v hv => ?_⟩
  have hv' : MsqValVA P.d P.n1 P.n2 v := hv (by simp [MsqValLA])
  simp only [MsqValVA, MsqNodeA] at hv'
  rcases hv' with h0 | h0 | h0 | h0 <;> rw [h0] <;> first | exact hd | exact h1 | exact h2 | simpa using h8

/-! ## `enq` in the value environment -/

/-- `enq`'s value table. -/
abbrev enqVTable (P : Params2) (F : Mem 64 → Prop) (n : BitVec 64) (ra : Int64) (t : MachineData) :
    Label → MachineData → (IVQ P).State → Prop :=
  fun lb s _ => F s.dmem ∧ s.lr = ra ∧ CalleeSaved t s ∧
    ((lb = "enq" ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = n) ∨
      (lb = "enq_loop" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = n) ∨
      (lb = "enq_fix" ∧ s.regs.X1.toBitVec = P.t ∧ s.regs.X2.toBitVec = n ∧ QV P s.regs.X4.toBitVec))

/-- **`enq` in the value environment**, frame `F` with `QFrameOK`: it writes
its node `n` to a link and to `tail`, and a link it read to `tail`. -/
theorem enqFrag_valF (P : Params2) (ht : P.t = P.h + 8) (F : Mem 64 → Prop) (hF : QFrameOK P (QG P) F)
    (n : BitVec 64) (hn : MsqNodeA P.d P.n1 P.n2 n) :
    FragSpecEnv (IVQ P) enqFrag "enq"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = n ∧ F s.dmem)
      (fun _ s _ s' _ => CalleeSaved s s') := by
  refine FragSpecEnv.of_cfg (fun ra t _ => enqVTable P F n ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, hd⟩ => ⟨hd, hlr, by simp [CalleeSaved], .inl ⟨rfl, hx0, hx1⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [enqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, hl8⟩ := hF _ hd
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [ht]; done)
  all_goals try (simp [hT.1, ht8]; done)
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA, QV]; done)
  case vc1 =>
    obtain ⟨hx0, hx1⟩ := hT
    exact ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, by simp (config := { decide := true }) [hx0, hx1, ht]⟩
  case vc7 =>
    rename_i s σ0 v3 σ1 v4 σ2 hnz hld1 hld2 _
    have hv3 : MsqValVA P.d P.n1 P.n2 v3 := by simpa [hT.1, MsqValLA] using hld1.1
    have hv4 : MsqValVA P.d P.n1 P.n2 v4 := by
      have h2 := hld2.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h2
      exact h2 (msqValLA_link hv3)
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, ?_⟩, .inl (by decide)⟩)
    simp (config := { decide := true }) [hT.1, hT.2]
    simpa [QV, MsqValVA] using hv4
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz hld1 hld2 _
    have hv3 : MsqValVA P.d P.n1 P.n2 v3 := by simpa [hT.1, MsqValLA] using hld1.1
    simp only [MsqValVA, MsqNodeA] at hv3
    rcases hv3 with h0 | h0 | h0 | h0 <;> simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, h0, hT.2] <;>
      exact fun old _ => msqValA_cas (.inr hn) old
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 hz old σ3 hnz hld1 hld2 hcas _
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, by simp (config := { decide := true }) [hT.1, hT.2]⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3; omega
  case vc14 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hT.1, hT.2]
    exact fun old _ => msqValA_cas (.inr hn) old
  case vc15 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩
  case vc3 =>
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hT.1]
    exact fun old _ => msqValA_cas hT.2.2 old
  case vc4 =>
    rename_i s σ0 old σ1 hcas _
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, by simp (config := { decide := true }) [hT.1, hT.2.1]⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h3 := hcas.2
    simp only [SharedEnv.tick_rmw] at h3; omega
  all_goals done

/-! ## `main` in any environment whose fences skip -/

/-- `main`'s precondition in any environment: `lookup`'s at `ra`, the queue
arguments, the private memory `d₀`. -/
def GPre (P : Params2) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) (t : MachineData) : Prop :=
  LookupPre x ra t ∧ t.regs.X25.toBitVec = P.h ∧ t.regs.X26.toBitVec = P.n1 ∧ t.regs.X27.toBitVec = P.n2 ∧
    t.dmem = d₀

section Pieces
variable [CodeEnv] (E : SharedEnv) [E.Skips]

theorem gmix_pre (P : Params2) (d₀ : Mem 64) (x : Tbl × Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => GPre P d₀ x ra s ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mPre⟩ : EnvProgram (SharedEnv.counted E))
    ⦃ (fun _ s _ => GPre P d₀ x ra s ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mPre
  vcgen
  all_goals obtain ⟨⟨⟨⟨h0, h1, h2, h3, h4, h30⟩, hm, hb, hpe⟩, h25, h26, h27, hd⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals subst hd
  all_goals simp [GPre, LookupPre, Args, h0, h1, h2, h3, h4, h30, h25, h26, h27, hm, hb, hpe]

theorem gmix_mid1 (P : Params2) (d₀ : Mem 64) (hd : Mem.loadInt d₀ P.n1 4 = none)
    (hs : ∀ k xcl v g, E.ok (.store k xcl P.n1 4 v) g) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => Keep P ra d₀ s ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mMid1⟩ : EnvProgram (SharedEnv.counted E))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.n1 ∧ Keep P ra d₀ s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mMid1
  vcgen
  all_goals obtain ⟨⟨h19, h25, h26, h27, hd0⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_ok] at *
  all_goals try (simp [h26]; exact hs _ _ _ _)
  all_goals subst hd0
  case vc3 =>
    rename_i hst _
    simp [h26, hd] at hst
    obtain ⟨rfl, -⟩ := hst
    exact ⟨by simp [h25], by simp [h26], by simpa using h19, by simp [h25], by simp [h26], by simp [h27], rfl⟩
  all_goals simp

theorem gmix_mid2 (P : Params2) (d₀ : Mem 64) (hd : Mem.loadInt d₀ P.n2 4 = none)
    (hs : ∀ k xcl v g, E.ok (.store k xcl P.n2 4 v) g) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => Keep P ra d₀ s ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mMid2⟩ : EnvProgram (SharedEnv.counted E))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = P.n2 ∧ Keep P ra d₀ s);
      fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mMid2
  vcgen
  all_goals obtain ⟨⟨h19, h25, h26, h27, hd0⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_ok] at *
  all_goals try (simp [h27]; exact hs _ _ _ _)
  all_goals subst hd0
  case vc3 =>
    rename_i hst _
    simp [h27, hd] at hst
    obtain ⟨rfl, -⟩ := hst
    exact ⟨by simp [h25], by simp [h27], by simpa using h19, by simp [h25], by simp [h26], by simp [h27], rfl⟩
  all_goals simp

theorem gmix_tail (P : Params2) (d₀ : Mem 64) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => Keep P ra d₀ s ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨mTail⟩ : EnvProgram (SharedEnv.counted E))
    ⦃ (fun _ _ _ => False); fun a _ _ => a = ra ⦄ := by
  intro s₀ g₀
  unfold mTail
  vcgen
  all_goals obtain ⟨⟨h19, -⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simpa using h19

end Pieces

/-- `Keep` survives a call whose callee keeps `CalleeSaved`. -/
theorem keep_of_cs {P : Params2} {ra ra' : Int64} {d₀ : Mem 64} {s s' : MachineData}
    (hk : Keep P ra d₀ s) (hc : CalleeSaved (s.setLr ra') s') : Keep P ra d₀ s' := by
  obtain ⟨h19, h25, h26, h27, hd⟩ := hk
  obtain ⟨c19, -, -, -, -, -, c25, c26, c27, -, cd⟩ := hc
  simp only [MachineData.setLr, Reg64s.setXReg] at c19 c25 c26 c27 cd
  exact ⟨by rw [c19]; exact h19, by rw [c25]; exact h25, by rw [c26]; exact h26, by rw [c27]; exact h27,
    by rw [cd]; exact hd⟩

/-- **`main` in any environment whose fences skip** -/
theorem mixMain_fragG (E : SharedEnv) [E.Skips] (P : Params2) (d₀ : Mem 64) (F : Mem 64 → Prop) (hd₀ : F d₀)
    (hn1 : Mem.loadInt d₀ P.n1 4 = none) (hn2 : Mem.loadInt d₀ P.n2 4 = none)
    (hs : ∀ m, m = P.n1 ∨ m = P.n2 → ∀ k xcl v g, E.ok (.store k xcl m 4 v) g)
    (henq : ∀ m, m = P.n1 ∨ m = P.n2 → FragSpecEnv (SharedEnv.counted E) enqFrag "enq"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.h ∧ s.regs.X1.toBitVec = m ∧ F s.dmem)
      (fun _ s _ s' _ => CalleeSaved s s'))
    (x : Tbl × Nat) :
    FragSpecEnvL (SharedEnv.counted E) [mixMain, flatLookup, enqFrag] "main"
      (fun ra t _ => GPre P d₀ x ra t) (fun _ _ _ _ _ => True) := by
  refine FragSpecEnvL.of_block mixMain_block fun hpl ra t g hpre => ?_
  have hLk := (MachineWP.FragSpecEnvL.ofProcSpec (frags := [flatLookup])
    (fun hpl' => lookup_spec (hpl' _ (by simp))) (SharedEnv.counted E) (SharedEnv.Skips.fenceInv_true _) x).at_sub
      hpl (by simp)
  have hE1 := (henq _ (.inl rfl)).toL.at_sub hpl (by simp)
  have hE2 := (henq _ (.inr rfl)).toL.at_sub hpl (by simp)
  have w1 := (gmix_pre E P d₀ x ra t g).le_wp t g ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at w1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w1)
  rintro s1 σ1 ⟨⟨⟨⟨h0, h1, h2, h3, h4, -⟩, hm, hb, hpe⟩, h25, h26, h27, hd⟩, h19⟩
  refine PartialWpEnv.call hLk fun ra' => ⟨?_, fun s2 σ2 hpost => ?_⟩
  · subst hd
    exact ⟨⟨by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h1, by simpa [MachineData.setLr, Reg64s.setXReg] using h2,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h3, by simpa [MachineData.setLr, Reg64s.setXReg] using h4,
      by simp [MachineData.setLr, Reg64s.setXReg]⟩, by simpa [MachineData.setLr] using hm, hb, hpe⟩
  obtain ⟨r, hr, hres, hdm, hcs⟩ := hpost
  simp only [Callee, MachineData.setLr, Reg64s.setXReg] at hcs hdm
  obtain ⟨-, c19, -, -, -, -, -, c25, c26, c27, -⟩ := hcs
  have w2 := (gmix_mid1 E P d₀ hn1 (hs _ (.inl rfl)) ra s2 σ2).le_wp s2 σ2
    ⟨⟨by rw [c19]; exact h19, by rw [c25]; exact h25, by rw [c26]; exact h26,
      by rw [c27]; exact h27, by rw [hdm]; exact hd⟩, rfl, rfl⟩
  rw [wpEnv_eq] at w2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w2)
  rintro s3 σ3 ⟨hx0, hx1, hk3⟩
  refine PartialWpEnv.call hE1 fun ra'' => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
    by simpa [MachineData.setLr, Reg64s.setXReg] using hx0, by simpa [MachineData.setLr, Reg64s.setXReg] using hx1,
    by simpa [MachineData.setLr, hk3.2.2.2.2] using hd₀⟩, fun s4 σ4 hc4 => ?_⟩
  have w3 := (gmix_mid2 E P d₀ hn2 (hs _ (.inr rfl)) ra s4 σ4).le_wp s4 σ4 ⟨keep_of_cs hk3 hc4, rfl, rfl⟩
  rw [wpEnv_eq] at w3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) w3)
  rintro s5 σ5 ⟨hx0', hx1', hk5⟩
  refine PartialWpEnv.call hE2 fun ra3 => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
    by simpa [MachineData.setLr, Reg64s.setXReg] using hx0', by simpa [MachineData.setLr, Reg64s.setXReg] using hx1',
    by simpa [MachineData.setLr, hk5.2.2.2.2] using hd₀⟩, fun s6 σ6 hc6 => ?_⟩
  have w4 := (gmix_tail E P d₀ ra s6 σ6).le_wp s6 σ6 ⟨keep_of_cs hk5 hc6, rfl, rfl⟩
  rw [wpEnv_eq] at w4
  exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun a s σ hra => ⟨hra, trivial⟩) w4)

/-! ## The dequeuer in the value environment -/

section D

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD)]

local instance progD.envV : CodeEnv := ⟨layout progD⟩

/-- `deq`'s value table. -/
abbrev deqVTable (P : Params2) (ra : Int64) (t0 : MachineData) : Label → MachineData → (IVQ P).State → Prop :=
  fun lb s _ => NoDmem s ∧ s.lr = ra ∧ CalleeSaved t0 s ∧ s.regs.X0.toBitVec = P.h ∧
    (lb = "deq" ∨ (lb = "deq_ne" ∧ QV P s.regs.X5.toBitVec))

theorem deq_valQ (P : Params2) (ht : P.t = P.h + 8) :
    FunSpecPartialEnv (IVQ P) ((_root_.Executable.labels cenv).label "deq")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.h ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, hx0, hD⟩
  refine cfgEnv_partial_fun_rank (p := deqFrag) (deqVTable P ra t0) MsqPilot.deqRank
    (E := fun a s (_ : (IVQ P).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD_placed (by decide)) t0 g
    ⟨hD, hlr, by simp [CalleeSaved], hx0, .inl rfl⟩
  cfg_cases_env_rank [deqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4⟩, hlr, hfr, hx0, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, MsqValLA, MsqValVA, MsqNodeA, QV]; done)
  case vc10 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hld1 hld2 hld3 _
    have hv3 : MsqValVA P.d P.n1 P.n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA P.d P.n1 P.n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4⟩,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, by simpa using hx0, ?_⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩)
    · simpa [QV, MsqValVA] using hv5
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3; omega
  case vc11 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hz hld1 hld2 hld3 _
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4⟩,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, by simpa using hx0, by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩)
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2
    simp only [SharedEnv.tick_load] at h1 h2 h3; omega
  case vc14 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz hld1 hld2 hld3 _
    have hv3 : MsqValVA P.d P.n1 P.n2 v3 := by simpa [hx0, MsqValLA] using hld1.1
    have hv5 : MsqValVA P.d P.n1 P.n2 v5 := by
      have h3 := hld3.1
      simp [SharedEnv.inv, Reg64s.setXReg] at h3
      exact h3 (msqValLA_link hv3)
    simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0, ht]
    exact fun old _ => msqValA_cas hv5 old
  case vc15 =>
    rename_i s σ0 v3 σ1 v4 σ2 v5 σ3 hne hnz old σ4 hld1 hld2 hld3 hcas _
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4⟩,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, by simpa using hx0, by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩)
    subst hg
    have h1 := hld1.2; have h2 := hld2.2; have h3 := hld3.2; have h4 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2 h3 h4; omega
  case vc1 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4⟩,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, by simpa using hx0, by simp⟩,
      .inl (by decide)⟩)
  case vc7 =>
    rename_i hld hcas _
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4⟩,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, by simpa using hx0, by simp⟩,
      .inr (.inr fun ⟨_, hg⟩ => ?_)⟩)
    subst hg
    have h4 := hcas.2
    simp only [SharedEnv.tick_rmw] at h4
    rcases hld with ⟨_, _, _, h3⟩ | ⟨_, _, ⟨_, h3⟩, _⟩
    · subst h3; omega
    · simp only [SharedEnv.tick_load] at h3; omega
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals first
    | (simp [SharedEnv.inv, Reg64s.setXReg, MsqValLA, hx0]
       exact fun old _ => msqValA_cas (by simpa [QV] using hT) old)
    | (rename_i hnz _ _ _ _
       simp [QV, MsqNodeA] at hT hnz
       rcases hT with h | h | h <;> simp [h]; done)

omit [Executable.ValidLayout (layout progD)] in
/-- `main_d`'s straight-line pieces before a call: the saved link, `q` in
`x0` and `x21`, no `dmem` word. -/
theorem mainD_piece_val (P : Params2) (p : Program) (hp : p = dPre ∨ p = dMid) :
    ∀ s₀ g₀, ⦃ fun s (σ : (IVQ P).State) => (Int64.ofBitVec (if p = dPre then s.regs.X30 else s.regs.X19).toBitVec
        = endD ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s) ∧ s = s₀ ∧ σ = g₀ ⦄ (⟨p⟩ : EnvProgram (IVQ P))
    ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧
        s.regs.X0.toBitVec = P.h ∧ NoDmem s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  rcases hp with rfl | rfl <;> simp only [show dMid ≠ dPre by decide, ↓reduceIte]
  · unfold dPre; vcgen
    all_goals obtain ⟨⟨h30, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp [NoDmem, h30, h21, hd8, hd4]
  · unfold dMid; vcgen
    all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp [NoDmem, h19, h21, hd8, hd4]

omit [Executable.ValidLayout (layout progD)] in
theorem mainD_tail_val (P : Params2) :
    ∀ s₀ g₀, ⦃ fun s (σ : (IVQ P).State) => Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨dTail⟩ : EnvProgram (IVQ P)) ⦃ (fun _ _ _ => False); fun a _ _ => a = endD ⦄ := by
  intro s₀ g₀
  unfold dTail
  vcgen
  all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  simpa using h19

/-- **The dequeuer's text in the value environment**: a `PartialTripleEnv` of
`progD` from its start, through `deq_valQ`. -/
theorem mainD_valQ (P : Params2) (ht : P.t = P.h + 8) :
    PartialTripleEnv (IVQ P) (fun s _ => Int64.ofBitVec s.regs.X30.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧
      NoDmem s) progD (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt progD "main_d" = some ⟨"main_d", mainDBody, some "deq"⟩ := by decide
  have call : ∀ s σ (rest : Program) (Q : MachineData → (IVQ P).State → Prop) E,
      Int64.ofBitVec s.regs.X19.toBitVec = endD ∧ s.regs.X21.toBitVec = P.h ∧ s.regs.X0.toBitVec = P.h ∧
        NoDmem s →
      (∀ s' σ', Int64.ofBitVec s'.regs.X19.toBitVec = endD ∧ s'.regs.X21.toBitVec = P.h ∧ NoDmem s' →
        PartialWpEnv (IVQ P) rest Q E s' σ') →
      PartialWpEnv (IVQ P) (blTo "deq" :: rest) Q E s σ := by
    rintro s σ rest Q E ⟨h19, h21, h0, ⟨hd8, hd4⟩⟩ hk
    refine PartialWpEnv.call (deq_valQ P ht) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩⟩, ?_⟩
    rintro s' σ' ⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩
    exact hk s' σ' ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
      ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩⟩
  have hbody : PartialWpEnv (IVQ P) mainDBody (fun _ _ => False) (fun a _ _ => a = endD) s σ := by
    have h1 := (mainD_piece_val P dPre (.inl rfl) s σ).le_wp s σ ⟨by simpa using hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1)
    refine fun s1 σ1 hA1 => call s1 σ1 _ _ _ hA1 fun s2 σ2 hB1 => ?_
    have h2 := (mainD_piece_val P dMid (.inr rfl) s2 σ2).le_wp s2 σ2
      ⟨by simpa [show dMid ≠ dPre by decide] using hB1, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h2)
    refine fun s3 σ3 hA2 => call s3 σ3 _ _ _ hA2 fun s4 σ4 hB2 => ?_
    have h3 := (mainD_tail_val P s4 σ4).le_wp s4 σ4 ⟨hB2.1, rfl, rfl⟩
    rw [wpEnv_eq] at h3
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3)
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD) progD [] 0 (by simp)
  rw [← progD_placed.entry pc hpc]
  refine (hbody _ (progD_placed.block _ _ hb)).mono fun x hx => .inl ⟨?_, trivial⟩
  rw [hx.resolve_left fun h => h.2, progD_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end D

end Kraken.Promising.Lower.Flat.Mix
