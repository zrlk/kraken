/-
**`MainWcPS.hW.rd`, `hra` and the buffer's words at rodata's own label** (AArch64,
`Level1I`'s `hP` stage 2): `wc_rodata` from the allocator's return inside the level
`WSHF … [frH env]` at `RdSrcL1`'s invariants (`jP'` … `jRet` at the labels `lbl` and rodata's label `l`), for any
`.sp0` invariant `Jp` below `rdCA l ini` at `RB lbl l` (`hJp`; `RdJpL.jpT_rb` at `Level1I`'s).

- `rd_ctl`: every control of the eight invariants is one of rodata's past the allocation (`RdPlS.RdCH`), with its
  term among `helloTerms`, and `.sp0`'s base is `l`'s place.
- `rdPostW_L1`: `RdWfSF.rdPostW_WSHF` at these, the placement `RdPlS.rdPostW_plS`, the controls' facts
  `HelloRdCf.hcf_frH`. Left: the buffer's words (`hbuf`), the saved return address (`hra`), the layout's immediates
  (`hI`), the frame's `me` (`hP`), the two exchanges' writes (`hwr1`, `hwr2`; `nodeW_wrC_rdX1/X2`).
- `hra_jpL`, `hra_jpLW`: `hra` (`MainWcPS`'s and `rdPostW_WSHF`'s forms) at a landing image `JpL` below the root's
  call invariant `mRdJ0 (rdJH lab J) σC` (`RdRa.hra_land`, `mNC`'s `x30`).
- `cellX0_jpL`: `.sp0`'s `x0` is an allocation's base (`RdBuf.CellX0`) at `JpL`, for `RdBuf.boxOkH_cellX0`.
-/
import Spike.Lib.A64HelloRdPostWfSF
import Spike.Lib.A64HelloRdPlS
import Spike.Lib.A64HelloRdJpL
import Spike.Lib.A64HelloRdBuf
import Spike.Lib.A64HelloRdRa

namespace Spike.Lib.A64.HelloPh.MainWcL1W

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (NodeW leave)
open Spike.Lib.A64.WakeWf (NoWrC)
open Spike.Lib.A64.HelloPh.WcW (freeNH BoxOkH)
open Spike.Lib.A64.HelloWf (WSHF)
open Spike.Lib.A64.Flow.HelloRd (pN RdPostW rN)
open Spike.Lib.A64.Flow.Hello1 (mR mF aR mRdJ0)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.RdSrcL1 (RB jP' jX1 jC2 jC2' jX3 jC4 jRet)
open Spike.Lib.A64.HelloPh.RdPlS (RdImms RdCH FrP)
open Spike.Lib.HelloRodataSrc (rdCA)
open Spike.Lib.HelloRdCf (frH)
open Spike.Lib (Arena FragS Ctl Region MemSide)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## The controls -/

section Ctl

variable {lbl : Lbl} {l : WeakMem.AllocLabel} {Jp : FAS → Ctl → Prop}

/-- **The eight invariants' controls** (module doc): `.sp0`'s base is `l`'s place, and the control is one of
rodata's past the allocation, its term among `helloTerms`. -/
theorem rd_ctl (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini) :
    ∀ σ0 c, (Jp σ0 c ∨ jP' lbl l σ0 c ∨ jX1 lbl l σ0 c ∨ jC2 lbl l σ0 c ∨ jC2' lbl l σ0 c ∨ jX3 lbl l σ0 c ∨
      jC4 lbl l σ0 c ∨ jRet lbl l σ0 c) →
      RB lbl l σ0 ∧ ∃ ini, RdCH l ini c ∧ c.term ∈ Spike.Lib.HelloRdCf.helloTerms := by
  intro σ0 c h
  have T := fun ini => Spike.Lib.HelloRdCf.rd_terms l ini default default
  rcases h with h | ⟨hB, ini, rfl⟩ | ⟨hB, ini, w, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ |
    ⟨hB, ini, wo0, w, rfl⟩ | ⟨hB, ini, wo0, wo1, rfl⟩ | ⟨hB, ini, wo0, wo1, rfl⟩
  · obtain ⟨hB, ini, rfl⟩ := hJp σ0 c h
    exact ⟨hB, ini, .inl ⟨rfl, rfl⟩, (T ini).2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inl ⟨rfl, rfl⟩⟩),
      (Spike.Lib.HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inl ⟨rfl, rfl⟩⟩)⟩),
      (Spike.Lib.HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inr (.inr ⟨rfl, rfl⟩)⟩)⟩),
      (Spike.Lib.HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.2.2⟩

end Ctl

/-! ## `hW.rd` -/

section Rd

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  {env : TermRun.Env}
  (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = Spike.Lib.A64.WakePh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`MainWcPS.hW.rd` at rodata's label** (module doc): `wc_rodata` from the allocator's return inside
`WSHF … [frH env]` in the region `mR R`, frame condition `mF R F m0 σC`, at `RdSrcL1`'s invariants. -/
theorem rdPostW_L1 (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hRlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {l : WeakMem.AllocLabel} {m0 : MachineData} {σC : FAS} {Jp : FAS → Ctl → Prop}
    (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini)
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      BoxOkH L.Λ L a (mF R F m0 σC) (Spike.Lib.A64.Flow.rAddr σ0.regs .X0 i))
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot (-8) = (L.lab ".L1_scc_rt_main.sp0").toBitVec)
    (hI : RdImms L.Λ) (hP : FrP lbl R env σC)
    (hwr1 : NodeW (NoWrC ar Spike.Lib.HelloSrc.helloSrc lbl lsize Ctx [frH env]) (fun _ _ => False) L.exe
      L.endPc (mR R) (mF R F m0 σC)
      (pN L.lab Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) (jC4 lbl l) (jRet lbl l) .x1))
    (hwr2 : NodeW (NoWrC ar Spike.Lib.HelloSrc.helloSrc lbl lsize Ctx [frH env]) (fun _ _ => False) L.exe
      L.endPc (mR R) (mF R F m0 σC)
      (pN L.lab Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) (jC4 lbl l) (jRet lbl l) .x2)) :
    RdPostW (WSHF L a ar Spike.Lib.HelloSrc.helloSrc Dt Cl Ctx lbl lsize (frH env) X0 [frH env])
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (mR R) (mF R F m0 σC)
      Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) (jC4 lbl l) (jRet lbl l) := by
  obtain ⟨hmR, halR, -⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok (F := fun _ => True) hR hal (fun _ _ _ _ => trivial)
    hRlo hhi m0 σC
  have hC := rd_ctl hJp
  exact Spike.Lib.A64.HelloPh.RdWfSF.rdPostW_WSHF (fs := [frH env]) (frM := frH env) (rS := rS) hp hlo hΛ hlab
    hsite hcl hX0 (.inr rfl) hmR halR (by simp only [mR, Region.callee]; omega)
    (by simp only [mR, Region.callee]; omega) hbuf hra
    (fun σ0 c h => let ⟨_, _, _, ht⟩ := hC σ0 c h; Spike.Lib.HelloRdCf.hcf_frH ht)
    (Spike.Lib.A64.HelloPh.RdPlS.rdPostW_plS hI hP fun σ0 c h =>
      let ⟨hB, ini, hc, _⟩ := hC σ0 c h; ⟨l, ini, hB.1, hc⟩)
    hwr1 hwr2

end Rd

/-! ## `.sp0`'s facts at a landing image -/

section Land

variable {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64} {J : FAS → Ctl → Prop} {σC : FAS}
  {J0 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}

/-- **`MainWcPS.hra` at a landing image** below the root's call invariant: `.sp0`'s saved return address is
`scc_rt_main`'s `.sp0` (`mNC`'s `x30`, kept by the entry and the allocator, `RdRa.hra_land`). -/
theorem hra_jpL {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab J) σC) l b w σ c) :
    lab ".L1_scc_rt_main.sp0" = Int64.ofBitVec (σ.slot (-8)) := by
  obtain ⟨_, σx, σ', c0, _, hN, _, rfl⟩ := h
  exact Spike.Lib.A64.HelloPh.RdRa.hra_land (R := R) (σx := σx)
    (fun σe c h => let ⟨c', hc'⟩ := h.2.2; Spike.Lib.A64.HelloPh.RdRa.x30_mRdJ0 (c := c') ⟨h.1, hc'⟩) hN

/-- **`rdPostW_L1`'s `hra` at a landing image** (`hra_jpL`, the bit-vector form). -/
theorem hra_jpLW {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab J) σC) l b w σ c) :
    σ.slot (-8) = (lab ".L1_scc_rt_main.sp0").toBitVec := by
  rw [hra_jpL h, Int64.toBitVec_ofBitVec]

/-- **`.sp0`'s `x0` is an allocation's base at a landing image** (`RdBuf.cellX0_land`). -/
theorem cellX0_jpL {J1 : FAS → Ctl → Prop} {σ : FAS} {c : Ctl} (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) :
    Spike.Lib.A64.HelloPh.RdBuf.CellX0 ms₀ lab σ := by
  obtain ⟨q, σx, σ', c0, hx, _, _, rfl⟩ := h
  exact Spike.Lib.A64.HelloPh.RdBuf.cellX0_land (q := q) hx

end Land

end Spike.Lib.A64.HelloPh.MainWcL1W

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1W.rd_ctl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1W.rd_ctl

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1W.rdPostW_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1W.rdPostW_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpL

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpLW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpLW

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1W.cellX0_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1W.cellX0_jpL
