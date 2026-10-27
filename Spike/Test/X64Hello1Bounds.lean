/-
**`hello1`'s callee rooms fit its runtime calls** (x86-64; the twin of
`Spike/Test/A64Hello1Bounds.lean`): at `hello1o`'s output (the
certificate's, `hello1_out_eq`), the stack need table's rows are
`wc_rodata` (row frame 40, the frame's size 32 and the saved `%rbp`; need
40) and `wc_main` (88: size 80; need 88), and every choice of the bounds
(`Bounds2`, as `stackBounds2` picks them, `hello1_bounds2_exists`) gives
the setup call's region `R1 := (RS v).callee (-8 - Z - 8 - 0) (-D1) 8` and
`main`'s `R2` (at `D2`), relative to the callee's entry `%rsp` (the return
address at `[0, 8)`), whose frame record's region (`%rbp` at offset 0, the
entry `%rsp` less 8: `lo + 8`, `hi + 8`) has the premises

- `allocW2_w2Full`'s (x86-64) at `wc_rodata`, which calls `scc_rt_alloc`:
  `lo + 8 ≤ -fS - 8 + -160 - 32` and `16 ≤ hi + 8`, 8-aligned;
- the print path's at `wc_main`, which calls `scc_rt_print` (`print_fits`'s
  `T.lo ≤ -96` below the call's `%rsp`, `%rbp - fM`): `lo + 8 ≤ -fM - 96`.

The rows by one kernel decision on the certificate's literal output; the
rest by `omega` from `Bounds2`'s `nS + 48 + 208 ≤ D1`, `nM + 48 + 208 ≤ D2`
(`needDRX`).
-/
import Spike.Lib.LowerX64.H0InAssembledB
import Spike.Test.X64Hello1Closed2

namespace Spike.Test.X64Hello1Bounds

open Spike.Lib.LowerX64 (Bounds2 stackBounds2)
open Spike.Lib.X64 (swR)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1`'s rows**: `wc_rodata`'s row frame and need 40, `wc_main`'s
88 (one kernel decision on the certificate's literal output). -/
theorem hello1_rows :
    (Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs).place.need
        (Scc.Lower.Names.user "rodata")).map (fun r => (r.2.1, r.2.2)) = some (40, 40) ∧
      (Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
        SccCertificate.sizes SccCertificate.labelOffs).place.need
        (Scc.Lower.Names.user "main")).map (fun r => (r.2.1, r.2.2)) = some (88, 88) := by
  rw [Spike.Lib.LowerX64.hello1_out_eq, show SccCertificate.out = _ from SccCertificate.out_eq]
  decide +kernel

/-- **Every choice of `hello1`'s bounds fits its runtime calls** (see the
module docstring): at `wc_rodata` (size 32) `allocW2_w2Full`'s region
premises in the frame record's region, at `wc_main` (size 80) the print
path's. -/
theorem hello1_bounds2 {Lr : Spike.Lib.X64.Rt.RuntimeLayout} {L D1 D2 : Int} {lS lM : String}
    {fS nS fM nM : Nat}
    (hB : Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs Lr L D1 D2 lS lM fS nS fM nM)
    (v : BitVec 64) :
    let Z := (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1)).Z.toInt
    let RS := (swR v (-L) 0).callee (-8 - 0) (8 - L) 8
    let R1 := RS.callee (-8 - Z - 8 - 0) (-D1) 8
    let R2 := RS.callee (-8 - Z - 8 - 0) (-D2) 8
    fS = 32 ∧ fS % 16 = 0 ∧ R1.lo + 8 ≤ -(fS : Int) - 8 + -160 - 32 ∧ 16 ≤ R1.hi + 8 ∧ (R1.lo + 8) % 8 = 0 ∧
      (R1.hi + 8) % 8 = 0 ∧
      fM = 80 ∧ R2.lo + 8 ≤ -(fM : Int) - 96 ∧ 16 ≤ R2.hi + 8 ∧ (R2.lo + 8) % 8 = 0 ∧ (R2.hi + 8) % 8 = 0 := by
  intro Z RS R1 R2
  show fS = 32 ∧ fS % 16 = 0 ∧ -D1 + 8 ≤ -(fS : Int) - 8 + -160 - 32 ∧ (16 : Int) ≤ 8 + 8 ∧ (-D1 + 8) % 8 = 0 ∧
      ((8 : Int) + 8) % 8 = 0 ∧ fM = 80 ∧ -D2 + 8 ≤ -(fM : Int) - 96 ∧ (16 : Int) ≤ 8 + 8 ∧ (-D2 + 8) % 8 = 0 ∧
      ((8 : Int) + 8) % 8 = 0
  obtain ⟨hrS, -, -, hDS, -, hrM, -, -, hDM, -, -, -, -, -, -, -, hD1, -, hD2, -⟩ := hB
  obtain ⟨hS, hM⟩ := hello1_rows
  rw [hrS] at hS
  rw [hrM] at hM
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hS hM
  obtain ⟨hS1, rfl⟩ := hS
  obtain ⟨hM1, rfl⟩ := hM
  omega

/-- **`hello1`'s bounds exist** (`stackBounds2` at `hello1o`, at any layout
and configuration with `CfgNeedOk` whose placement check passes) and fit its
runtime calls (`hello1_bounds2`). -/
theorem hello1_bounds2_exists {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1)
      SccCertificate.sizes SccCertificate.labelOffs) = true)
    (hcfg : Spike.Lib.LowerX64.CfgNeedOk pcfg = true) (Lr : Spike.Lib.X64.Rt.RuntimeLayout) :
    ∃ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs Lr L D1 D2 lS lM fS nS fM nM ∧
      fS = 32 ∧ fM = 80 := by
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ :=
    stackBounds2 h Spike.Lib.LowerNode.hello1o_accepted2 (by decide) hcfg Lr
  exact ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB, (hello1_bounds2 hB 0).1, (hello1_bounds2 hB 0).2.2.2.2.2.2.1⟩

/-- info: 'Spike.Test.X64Hello1Bounds.hello1_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_rows

/-- info: 'Spike.Test.X64Hello1Bounds.hello1_bounds2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_bounds2

/--
info: 'Spike.Test.X64Hello1Bounds.hello1_bounds2_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hello1_bounds2_exists

end Spike.Test.X64Hello1Bounds
