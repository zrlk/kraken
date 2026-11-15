/-
**`hello1.w` after the granule pass, at the
linked post-pass executable's layout** (x86-64): `x64_scc_correctE_text_closedAt2_final` at the
post-pass output of `Spike/Test/X64Hello1GOut.lean`, the pre-pass output's placement check at the
post-pass layout (`Hello1LinkedX64G.pre_placeOKAt`), the post-pass output's (`post_placeOKAt`),
the tail's shape decided on the literals.
-/
import Spike.Test.X64Hello1GOut
import Spike.Test.Hello1LinkedX64GPost
import Spike.Lib.LowerX64.Closed2TailFinal

namespace Spike.Lib.LowerX64.Hello1G

set_option maxRecDepth 100000

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Test.X64Hello1GOut
open Spike.Test.Hello1LinkedX64G (ΛF pre_placeOKAt)
open Spike.Test.Hello1LinkedX64GPost (post_placeOKAt)

local notation "P1" => Spike.Test.Hello1MainSrc.hello1o
local notation "BT" => ["scc_text_end", ".Lgw0"]

/-- The pre-pass cells without the end label. -/
def P1cells : List (Directive × Nat) := SccCertificate.outLit.prog.dropLast
/-- The tail. -/
def T1 : List (Directive × Nat) := csLit.drop P1cells.length

theorem hPE0 : SccCertificate.outLit.prog = P1cells ++ [(.label "scc_text_end", 0)] := by kernel_rfl
theorem hPF0 : csLit = P1cells ++ T1 := by kernel_rfl
-- The three facts below quantify over labels and instructions; each is read off a `List.all`
-- check decided on the literal.

theorem hT1 : ∀ dz ∈ T1, ∀ l, dz.1 = .label l → l ∈ BT := by
  have h : T1.all (fun dz => match dz.1 with | .label l => decide (l ∈ BT) | _ => true) = true := by
    decide +kernel
  intro dz hd l he
  have := List.all_eq_true.1 h dz hd
  rw [he] at this
  simpa using this

theorem hTi1 : ∀ dz ∈ T1, ∀ i, dz.1 ≠ .instr i := by
  have h : T1.all (fun dz => match dz.1 with | .instr _ => false | _ => true) = true := by
    decide +kernel
  intro dz hd i he
  have := List.all_eq_true.1 h dz hd
  rw [he] at this
  exact Bool.false_ne_true this

theorem hfree1 : ∀ i z, (Directive.instr i, z) ∈ P1cells → Spike.Lib.X64LabelCongr.Directive.Free BT (.instr i) := by
  have h : P1cells.all (fun dz => decide (Spike.Lib.X64LabelCongr.Directive.Free BT dz.1)) = true := by
    decide +kernel
  intro i z hm
  exact of_decide_eq_true (List.all_eq_true.1 h _ hm)

/-- `hello1o` lowers at `configW` to the certificate's literals. -/
theorem hL1 : lowered1 SccCertificate.configW P1 = some (SccCertificate.loweredLit.1, SccCertificate.loweredLit.2) :=
  lowered1_of_stages (fr := SccCertificate.framesLit) (by kernel_rfl) (by kernel_rfl)

/-- `hello1o`'s output at `configW` is the certificate's. -/
theorem outW_eq : Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.configW P1) SccCertificate.sizes
    SccCertificate.labelOffs = SccCertificate.outLit :=
  (ofEmitted_of_stages SccCertificate.sizes SccCertificate.labelOffs hL1 SccCertificate.emitted_eq
      SccCertificate.tables_eq).trans
    ((ofEmitted_of_stages SccCertificate.sizes SccCertificate.labelOffs (ir := SccCertificate.loweredLit.1)
      (setup := SccCertificate.loweredLit.2) SccCertificate.lowered_eq SccCertificate.emitted_eq
      SccCertificate.tables_eq).symm.trans (SccCertificate.out_eqW.symm.trans SccCertificate.out_eq))

/-- The pre-pass output, as `hello1o` lowers at `configW`, passes the placement check at the
post-pass layout. -/
theorem hE1 : placeOKAt SccCertificate.placeCfg ΛF
    (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.configW P1) SccCertificate.sizes
      SccCertificate.labelOffs) = true := by
  rw [outW_eq, ← SccCertificate.out_eq]; exact pre_placeOKAt

/-- The post-pass output passes the placement check at the post-pass layout. -/
theorem hF1 : placeOKAt SccCertificate.placeCfg ΛF oF = true := oF_eq ▸ post_placeOKAt

/-- **`hello1`'s x86-64 statement at the post-pass text at the linked post-pass executable's
layout**, given the parse of the text (`hpaF`, the compiled `#guard` below). -/
theorem hello1_finalCF
    (hpaF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oF.prog oF.secs = true)
    {Bu : Scc.Sem.Budget} (hB : Bu.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 ΛF P1) Bu
      ⟨textF, sizesFLit, offsFLit⟩ :=
  x64_scc_correctE_text_closedAt2_final SccCertificate.configW (by decide)
    Spike.Lib.LowerNode.hello1o_accepted2 (by decide) hE1 (by decide) hL1 SccCertificate.emitted_eq
    SccCertificate.tables_eq hcF hzF hbF hF1 (outW_eq ▸ hPE0) hPF0
    (by decide) hT1 hTi1 hfree1 (fun k => by cases k <;> decide) (fun k => by cases k <;> decide +kernel)
    (by decide) (by decide) hpaF hB

end Spike.Lib.LowerX64.Hello1G

/-- info: 'Spike.Lib.LowerX64.Hello1G.hello1_finalCF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.Hello1G.hello1_finalCF
