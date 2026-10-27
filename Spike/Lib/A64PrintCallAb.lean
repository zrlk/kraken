/-
**A call of `print` with the refusal's data** (AArch64): the calls of
`Spike/Lib/A64PrintCall.lean` and `Spike/Lib/A64RtAbortSeg.lean` with the
callee `PrintAb.seg_printAb_ofW` (`Spike/Lib/A64PrintAb.lean`: the
refusal branch of the result's classification a `Refusal` of the bytes
left) in place of `PrintA.seg_printA_ofW`. The premises are the same but
`print`'s block obligations, asked at `PrintAb`'s nodes (`PrintAbW`).

- `PrintAb.PrintAbW.mono`: `PrintAbW` under a stronger frame condition;
- `PrintCallAb.pN`, `pE`, `pNe`: `print`'s nodes, exits and pinned entry for
  the call state (with `PrintCall.pR`, `pF`, `pcS` unchanged);
- `print_callAbW`, `print_call_segAbW`, `print_call_abort_segAbW`: as
  `print_callW`, `print_call_segW`, `print_call_abort_segW`.

The count passed to `print` is below `2^63` as there: `print_callAbW`
asks it (`hlen`), `print_call_segAbW` and `print_call_abort_segAbW` derive
it from `x1 = printN n m` and `8·m < 2^63` (`hN`, `hm`; `printSite_x1`).
-/
import Spike.Lib.A64PrintAb
import Spike.Lib.A64RtAbortSeg

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Spike.Lib.A64.Flow.Ret0 (CallerCells blkW_mono)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD printBody print_entry_run printC_entry
  printC_load printC_next)
open RtAbort (PrintFits paN)

/-- `PrintAbW` under a weaker frame condition holds under a stronger one. -/
theorem _root_.Spike.Lib.A64.PrintAb.PrintAbW.mono {W : Frag isaLSE2} {K : State → State → Prop}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F' : MachineData → Prop} {x29 ra buf0 : BitVec 64}
    {len0 : Nat} {P Q : Nat → Ctl → Prop}
    (h : PrintAb.PrintAbW x29 ra buf0 len0 P Q W K exe endPc R F) (hFF : ∀ m, F' m → F m) :
    PrintAb.PrintAbW x29 ra buf0 len0 P Q W K exe endPc R F' :=
  ⟨blkW_mono h.e hFF, blkW_mono h.n1 hFF, blkW_mono h.loop hFF, blkW_mono h.n3 hFF, blkW_mono h.write hFF,
    blkW_mono h.n5 hFF, blkW_mono h.n6 hFF, blkW_mono h.n7 hFF, blkW_mono h.chk2 hFF, blkW_mono h.n9 hFF,
    blkW_mono h.n10 hFF, blkW_mono h.chk3 hFF, blkW_mono h.n12 hFF, blkW_mono h.adv hFF, blkW_mono h.fail hFF,
    blkW_mono h.done hFF⟩

/-! ## The call -/

namespace PrintCallAb

variable (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (kc : Int)

/-- `print`'s nodes for the call state `σC`. -/
abbrev pN (σC : AS) : Print.PN → ND :=
  PrintAb.N lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat
    (Pc σC) (Qc σC)

/-- `print`'s exits for the call state `σC`. -/
abbrev pE (σC : AS) : Print.PX → ND :=
  PrintAb.E lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC)

/-- `print`'s entry, pinned to the call state `σC` entered at `kc`. -/
def pNe (σC : AS) : ND :=
  ⟨(pN lab Pc Qc σC .e).pc, (pN lab Pc Qc σC .e).o, fun σ c => (pN lab Pc Qc σC .e).J σ c ∧ σ = enter kc σC⟩

end PrintCallAb

open PrintCallAb
open PrintCall (pR pF pcS)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` is one segment inside `W`**, from any call node
`nC` (pc `scc_rt_print`, `sp` offset `nC.o.sp` 16-aligned with `print`'s
48 bytes inside `R`) to the caller's nodes `N` and exits `E`: `call_nd_FWK`
with `seg_printAb_ofW`, for any source predicates `Pc`/`Qc` of the call
state (see the module docstring). -/
theorem print_callAbW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintAb.PrintAbW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) W K exe endPc (pR nC.o.sp R) (pF nC.o.sp R F))
    (hsvc : ∀ F' : MachineData → Prop, FStable (pR nC.o.sp R) F' → (∀ m, F' m → pF nC.o.sp R F m) →
      ∀ σC c, nC.J σC c →
      SegW W K p lbl ms (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc))
        (At exe endPc (pR nC.o.sp R) F' (pN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine call_nd_FWK (KC := False) (lo' := -48) (hi' := 0) (M := fun _ => True)
    (Ne := pNe lab Pc Qc nC.o.sp) (Ex := pE lab Pc Qc)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide) (fun h => h.elim) (fun h => h.elim)
    (fun _ h _ => h)
    (fun R' F' hR' hal' hlo' hhi' hF' _ hFF hR'e hcc g hg _ => by
      subst hR'e
      obtain ⟨σC, c, hJ, ⟨-, he⟩⟩ := hg
      have hσ : σC = g := enter_inj he
      subst hσ
      have hF'' : ∀ m, F' m → pF nC.o.sp R F m := fun m h => ⟨hFF m h, hcc m h⟩
      refine ((PrintAb.seg_printAb_ofW hp hend hprog hF' hR' hal' hlo' hhi' (hlen σC c hJ)
        ((hW σC c hJ).mono hF'') (hsvc F' hF' hF'' σC c hJ)).mono_pre ?_).mono_post
          fun _ _ ⟨y, h⟩ => ⟨y, h, trivial⟩
      rintro s c ⟨a, b, d, e, σ, hA, hD, hJ', -⟩
      exact ⟨a, b, d, e, σ, hA, hD, hJ'⟩)
    (fun _ => rfl) ?_ ?_
  · intro σC c hJ
    exact ⟨σC, hpc.symm, ⟨hP0 σC c hJ, rfl, rfl, rfl, by simp [enter]⟩, rfl⟩
  · rintro g y σC c σx c' σR hJ ⟨-, he⟩ hx hreg - hsl
    have hσ : σC = g := enter_inj he
    subst hσ
    cases y
    · obtain ⟨h29, h30, hP⟩ := hx
      have h := hret σC c σR c' hJ (by rw [hreg]; exact h29) (by rw [hreg]; exact h30) hP hsl
      simpa [pE, PrintAb.E, Print.oE] using h
    · obtain ⟨h4, k, hQ⟩ := hx
      exact habort σC c σR c' k hJ (by rw [hreg]; exact h4) hQ hsl

/-- **A call of `print` against the source's loop is one segment inside
`W`**: `print_callAbW` with `Pc = Qc = pcS …` and its write system call from
the output row (`hE`, its byte step `BO` closed under local runs, `hcl`),
the byte steps from the row's load-and-emit at the source's element load
(`hlb`) and the source's loop (`printC_load`, `printC_next`). The call
site gives register facts only: `x1 = printN n m` (`hN`) and `8·m < 2^63`
(`hm`); see `printSite_x1`. -/
theorem print_call_segAbW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintAb.PrintAbW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  have hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63 := fun σ c hJ => by
    have := hN σ c hJ; have := hm σ c hJ; unfold printN at *; omega
  refine print_callAbW hp hend hprog hF hR hal hlo hhi hk16 hpc hP0 hlen hW ?_
    (fun σC c σR c' hJ h29 h30 hP hsl => hret σC c σR c' hJ h29 h30 (hN σC c hJ ▸ hP) hsl) habort
  intro F' hF' _ σC c hJ
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] at hpr
  refine PrintAb.hsvc_of_emit hE hK hF' (fun _ _ _ => hlen σC c hJ) ?_ (hWs σC c hJ F') (fun _ _ h => h) ?_
    (hwe σC c hJ F')
  · exact Scc.Cert.Rt.A64.Print.code_field hp hend hpr.2.2.2.2.2.1
      (by simp only [PrintAb.N, Print.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
  · intro s c' hAt k j c1 hlt hP
    have hk : k + j < printN (n σC) (m σC) := by rw [← hN σC c hJ]; exact hlt
    obtain ⟨_, _, -, -, -, -, -, -, hwn⟩ := id hP
    refine hcl _ _ _ _ _ _ (printC_load hd hP hk).toLocalRun (hlb σC c hJ F' s c' hAt k j hk) ?_
    rintro _ ⟨mw, b, rfl⟩
    obtain ⟨c2, r, hc2⟩ := printC_next (mw := mw) (b := b) hd hwn hk
    exact ⟨c2, r.toLocalRun, hc2⟩

/-- **A call of `print` with its abort path is one segment inside `W`**,
from any call node `nC` to the caller's nodes `N` and exits `E`:
`print_call_segAbW`, its abort landing at `paN` (`print`'s abort exit, `sp`
at `nC.o.sp - 48`), and from there `seg_jabort4W` (the dispatcher at the
write code and `scc_rt_abort_write`, in the region below), which does not
return. The caller's region below the `bl` is `T` (`hTR`), with `print`'s
region facts there (`hfit`, as `RtDepthA64.print_fits` gives them): they
give `print_call_segAbW`'s `hlo` and the abort path's. The abort path's
obligations are asked at `paN`'s states (`hstub`); the other premises are
`print_call_segAbW`'s. -/
theorem print_call_abort_segAbW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat} {T : Region}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hTR : R.lo ≤ nC.o.sp + T.lo) (hfit : PrintFits T)
    (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintAb.PrintAbW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    -- the abort path below `print`'s abort exit
    (hstub : ∀ m0 σA c0, (paN (_root_.Executable.labels exe).label R nC pw wn n m).J σA c0 →
      Abort.Disp.StubWW W K p lbl ms exe endPc (R.callee (nC.o.sp + -48) (-48) 0)
        (fun m' => F m' ∧ CKept R (nC.o.sp + -48) (-48) 0 m0 m' ∧ Abs R ⟨nC.o.sp + -48, []⟩ m0 σA) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  refine SegW.of_someJ fun _ c0 _ => ?_
  have hT : T.lo ≤ -96 := hfit.lo c0
  let nA := paN (_root_.Executable.labels exe).label R nC pw wn n m
  have hA : SegW W K p lbl ms (At exe endPc R F nA) (Next exe endPc R F N E) :=
    Abort.Disp.seg_jabort4W (nC := nA) rfl (fun σ c h => by rw [h.1]; rfl) hF hR hal
      (by show R.lo ≤ nC.o.sp + -48 - 48; omega) (by show nC.o.sp + -48 < R.hi; omega)
      (by show (nC.o.sp + -48) % 16 = 0; omega) hK hstub
  have h1 := print_call_segAbW (N := fun x : PSum ι PUnit.{1} => match x with | .inl i => N i | .inr _ => nA) (E := E)
    hp hend hprog hF hR hal (by omega) hhi hk16 hpc hP0 hN hm hW hd hE hK hcl hWs hlb hwe
    (fun σC c σR c' hJ h29 h30 hP hsl => (hret σC c σR c' hJ h29 h30 hP hsl).elim
      (fun ⟨j, h⟩ => .inl ⟨.inl j, h⟩) .inr)
    (fun σC c σR c' k hJ h4 hP hsl => .inl ⟨.inr ⟨⟩, rfl, by simp [SO.le, nA, paN], h4, σC, c, k, hJ, hP, hsl⟩)
  refine ((h1.mono_post ?_).seq_left hA).mono_post fun _ _ h => h.elim id id
  rintro s c (⟨⟨j⟩ | ⟨⟩, h⟩ | h)
  · exact .inr (.inl ⟨j, h⟩)
  · exact .inl h
  · exact .inr (.inr h)

end Fn

end Spike.Lib.A64.Flow
