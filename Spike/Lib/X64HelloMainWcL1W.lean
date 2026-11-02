/-
**`MainWcPS.hW.rd` and `hra` at rodata's own label** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1W.lean`'s live
part): `wc_rodata` from the allocator's return inside the level `WSHF … [frH env]` at `RdSrcL1`'s invariants
(`jP'` … `jX3` at the labels `lbl` and rodata's label `l`), for any `.x15` invariant `Jp` below `rdCA l ini` at
`RB lbl l` (`hJp`; `RdJpL.jpT_rb` at `Level1I`'s), and any last-block invariant `J4` whose controls are rodata's
from the publication on (`hJ4`).

- `rd_ctl`: every control of the seven invariants is one of rodata's past the allocation (`RdPlS.RdCH`), with its
  term among `helloTerms`, and `.x15`'s base is `l`'s place.
- `rdPostW_L1`: `RdWfSF.rdPostW_WSHF` at these, the placement `RdPlS.rdPostW_plS`, the controls' facts
  `HelloRdCf.hcf_frH`. Left: the buffer's words (`hbuf`), the return address (`hra`), the layout's immediates
  (`hI`), the frame's `me` (`hP`), the two exchanges' writes (`hwr1`, `hwr2`).
- `hra_jpL`, `hra_jpLW`: `hra` (`MainWcPS`'s and `rdPostW_WSHF`'s forms) at a landing image `JpL` below the root's
  call invariant `mRdJ0 (rdJH lab R' J) σC` (`RdRa.hra_land`, `mNC`'s return address).

## Differences from the AArch64 version

- `.x15` has seven invariants (AArch64 `.sp0`, eight): there is no fence node, and `MainWcPS.hW`'s last one is
  `HelloRd.J4P p J4 J5` (the publication a source stutter). `rd_ctl` and `rdPostW_L1` take that last invariant
  as a parameter `J4` with `hJ4`: its controls are `rdC4`, `rdC5` or `rdRet` (AArch64: `jC4`, `jRet` fixed).
- `hra` is the return address `.Lscc_rt_main.x2` at `σ0.slot 0` (AArch64 `.L1_scc_rt_main.sp0` at `-8`).
- The region's bounds are x86-64's (`R.lo ≤ -288`, `8 ≤ R.hi`, no alignment); `mR R`'s are `rdPostW_WSHF`'s.
- `rdJH` takes `scc_rt_main`'s region `R'` (x86-64's `mNC` pins `%rbp` in it).
- No `RdBuf` import: its only use is `cellX0_jpL`'s.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `cellX0_jpL`.
-/
import Spike.Lib.X64HelloRdPostWfSF
import Spike.Lib.X64HelloRdPlS
import Spike.Lib.X64HelloRdJpL
import Spike.Lib.X64HelloRdRa

namespace Spike.Lib.X64.HelloPh.MainWcL1W

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (NodeW leave bAddr)
open Spike.Lib.X64.WakeWf (NoWrC)
open Spike.Lib.X64.HelloPh.WcW (freeNH BoxOkH)
open Spike.Lib.X64.HelloWf (WSHF)
open Spike.Lib.X64.Flow.HelloRd (pN RdPostW rN)
open Spike.Lib.X64.Flow.Hello1 (mR mF aR mRdJ0)
open Spike.Lib.X64.HelloPh.Level1 (JpL)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.RdSrcL1 (RB jP' jX1 jC2 jC2' jX3)
open Spike.Lib.X64.HelloPh.RdPlS (RdImms RdCH FrP)
open Spike.Lib.X64HelloRodataSrc (rdCA rdC4 rdC5 rdRet)
open Spike.Lib.X64HelloRdCf (frH)
open Spike.Lib (Arena FragS Ctl Region MemSide)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The controls -/

section Ctl

variable {lbl : Lbl} {l : WeakMem.AllocLabel} {Jp J4 : FAS → Ctl → Prop}

/-- **The seven invariants' controls** (module doc): `.x15`'s base is `l`'s place, and the control is one of
rodata's past the allocation, its term among `helloTerms`. -/
theorem rd_ctl (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini)
    (hJ4 : ∀ σ0 c, J4 σ0 c → RB lbl l σ0 ∧ ∃ ini wo0 wo1,
      c = rdC4 l ini wo0 wo1 ∨ c = rdC5 l ini wo0 wo1 ∨ c = rdRet l ini wo0 wo1) :
    ∀ σ0 c, (Jp σ0 c ∨ jP' lbl l σ0 c ∨ jX1 lbl l σ0 c ∨ jC2 lbl l σ0 c ∨ jC2' lbl l σ0 c ∨ jX3 lbl l σ0 c ∨
      J4 σ0 c) →
      RB lbl l σ0 ∧ ∃ ini, RdCH l ini c ∧ c.term ∈ Spike.Lib.X64HelloRdCf.helloTerms := by
  intro σ0 c h
  have T := fun ini => Spike.Lib.X64HelloRdCf.rd_terms l ini default default
  rcases h with h | ⟨hB, ini, rfl⟩ | ⟨hB, ini, w, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ |
    ⟨hB, ini, wo0, w, rfl⟩ | h
  · obtain ⟨hB, ini, rfl⟩ := hJp σ0 c h
    exact ⟨hB, ini, .inl ⟨rfl, rfl⟩, (T ini).2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inl ⟨rfl, rfl⟩⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · obtain ⟨hB, ini, wo0, wo1, rfl | rfl | rfl⟩ := hJ4 σ0 c h
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inl ⟨rfl, rfl⟩⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.1⟩
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inr (.inl ⟨rfl, rfl⟩)⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.2.1⟩
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inr (.inr ⟨rfl, rfl⟩)⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.2.2⟩

end Ctl

/-! ## `hW.rd` -/

section Rd

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {X0 : State → Prop}
  {env : TermRun.Env}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)

include hp hlo hΛ hlab hsite hcl hX0

/-- **`MainWcPS.hW.rd` at rodata's label** (module doc): `wc_rodata` from the allocator's return inside
`WSHF … [frH env]` in the region `mR R`, frame condition `mF R F m0 σC`, at `RdSrcL1`'s invariants and the last
block's `J4`. -/
theorem rdPostW_L1 (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {l : WeakMem.AllocLabel} {m0 : MachineData} {σC : FAS} {Jp J4 : FAS → Ctl → Prop}
    (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini)
    (hJ4 : ∀ σ0 c, J4 σ0 c → RB lbl l σ0 ∧ ∃ ini wo0 wo1,
      c = rdC4 l ini wo0 wo1 ∨ c = rdC5 l ini wo0 wo1 ∨ c = rdRet l ini wo0 wo1)
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      BoxOkH L.Λ L a (mF R F m0 σC) (bAddr σ0.regs .rax i))
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot 0 = (L.lab ".Lscc_rt_main.x2").toBitVec)
    (hI : RdImms L.Λ) (hP : FrP lbl R env σC)
    (hwr1 : NodeW (NoWrC ar Spike.Lib.X64HelloSrc.helloSrc lbl lsize Ctx [frH env]) (fun _ _ => False) L.exe
      L.endPc (mR R) (mF R F m0 σC)
      (pN L.lab Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) J4 .x1))
    (hwr2 : NodeW (NoWrC ar Spike.Lib.X64HelloSrc.helloSrc lbl lsize Ctx [frH env]) (fun _ _ => False) L.exe
      L.endPc (mR R) (mF R F m0 σC)
      (pN L.lab Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) J4 .x2)) :
    RdPostW (WSHF L a ar Spike.Lib.X64HelloSrc.helloSrc Dt Cl Ctx lbl lsize (frH env) X0 [frH env])
      (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc (mR R) (mF R F m0 σC)
      Jp (jP' lbl l) (jX1 lbl l) (jC2 lbl l) (jC2' lbl l) (jX3 lbl l) J4 := by
  have hmR := (Spike.Lib.X64.Flow.Hello1.mR_ok (F := fun _ => True) hR (fun _ _ _ _ => trivial) hRlo hhi m0 σC).1
  have hC := rd_ctl hJp hJ4
  exact Spike.Lib.X64.HelloPh.RdWfSF.rdPostW_WSHF (fs := [frH env]) (frM := frH env) (rS := rS) hp hlo hΛ hlab
    hsite hcl hX0 (.inr rfl) hmR (by simp only [mR, Region.callee]; omega)
    (by simp only [mR, Region.callee]; omega) hbuf hra
    (fun σ0 c h => let ⟨_, _, _, ht⟩ := hC σ0 c h; Spike.Lib.X64HelloRdCf.hcf_frH ht)
    (Spike.Lib.X64.HelloPh.RdPlS.rdPostW_plS hI hP fun σ0 c h =>
      let ⟨hB, ini, hc, _⟩ := hC σ0 c h; ⟨l, ini, hB.1, hc⟩)
    hwr1 hwr2

end Rd

/-! ## `.x15`'s facts at a landing image -/

section Land

variable {R R' : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J : FAS → Ctl → Prop} {σC : FAS}
  {J0 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}

/-- **`MainWcPS.hra` at a landing image** below the root's call invariant: `.x15`'s return address is
`scc_rt_main`'s `.x2` (`mNC`'s, kept by the entry and the allocator, `RdRa.hra_land`). -/
theorem hra_jpL {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b w σ c) :
    lab ".Lscc_rt_main.x2" = Int64.ofBitVec (σ.slot 0) := by
  obtain ⟨_, σx, σ', c0, _, hN, _, rfl⟩ := h
  exact Spike.Lib.X64.HelloPh.RdRa.hra_land (R := R) (σx := σx)
    (fun σe c h => let ⟨c', hc'⟩ := h.2.2; Spike.Lib.X64.HelloPh.RdRa.x30_mRdJ0 (c := c') ⟨h.1, hc'⟩) hN

/-- **`rdPostW_L1`'s `hra` at a landing image** (`hra_jpL`, the bit-vector form). -/
theorem hra_jpLW {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b w σ c) :
    σ.slot 0 = (lab ".Lscc_rt_main.x2").toBitVec := by
  rw [hra_jpL h, Int64.toBitVec_ofBitVec]

end Land

end Spike.Lib.X64.HelloPh.MainWcL1W

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.rd_ctl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.rd_ctl

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.rdPostW_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.rdPostW_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpL

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW
