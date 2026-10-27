/-
**`hello1`'s callee rooms fit its runtime calls** (AArch64): at `hello1o`'s
output (the certificate's, `hello1_out_eqA`), the stack need table's rows
are `wc_rodata` (frame 48, need 48) and `wc_main` (frame 96, need 96), and
every choice of the bounds (`Bounds2A`, as `stackBounds2A` picks them,
`hello1_bounds2A_exists`) gives the setup call's region
`(swR v (-L) 0).callee (-Z) (-D1) 0` and `main`'s
`(swR v (-L) 0).callee (-Z) (-D2) 0` the premises

- `allocW2_w2Full`'s at `wc_rodata`, which calls `scc_rt_alloc`: the frame
  `fS = 48` (`≤ 4095`, 16-aligned), `R.lo ≤ -fS + -160 - 48`, `0 ≤ R.hi`, the
  bounds 8-aligned;
- the print path's at `wc_main`, which calls `scc_rt_print` (`print_fits`'s
  `T.lo ≤ -96` below the frame): `R.lo ≤ -fM - 96`, `0 ≤ R.hi`, 8-aligned.

The rows by one kernel decision on the certificate's literal output; the
rest by `omega` from `Bounds2A`'s `nS + 48 + 208 ≤ D1`, `nM + 48 + 208 ≤ D2`
(`needDR`). With the rooms `needDA n` alone neither would hold (`96 < 256`,
`144 < 192`).
-/
import Spike.Lib.LowerA64.H0InAssembledBA
import Spike.Test.A64Hello1Closed2

namespace Spike.Test.A64Hello1Bounds

open Spike.Lib.LowerA64 (Bounds2A stackBounds2A)
open Spike.Lib.A64.Flow (swR)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1`'s rows**: `wc_rodata`'s frame and need 48, `wc_main`'s 96
(one kernel decision on the certificate's literal output). -/
theorem hello1_rowsA :
    (Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)).place.need
        (Scc.Lower.Names.user "rodata")).map (fun r => (r.2.1, r.2.2)) = some (48, 48) ∧
      (Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)).place.need
        (Scc.Lower.Names.user "main")).map (fun r => (r.2.1, r.2.2)) = some (96, 96) := by
  rw [Spike.Lib.LowerA64.hello1_out_eqA, show SccCertificate.out = _ from SccCertificate.out_eq]
  decide +kernel

/-- **Every choice of `hello1`'s bounds fits its runtime calls** (see the
module docstring): at `wc_rodata` (frame 48) `allocW2_w2Full`'s region
premises, at `wc_main` (frame 96) the print path's. -/
theorem hello1_bounds2A {Lr : Spike.Lib.A64.Rt.RuntimeLayout} {L D1 D2 : Int} {lS lM : String}
    {fS nS fM nM : Nat} (hB : Bounds2A SccCertificate.config P1A Lr L D1 D2 lS lM fS nS fM nM) (v : BitVec 64) :
    let Z := (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1A)).Z.toInt
    let R1 := (swR v (-L) 0).callee (-Z) (-D1) 0
    let R2 := (swR v (-L) 0).callee (-Z) (-D2) 0
    fS = 48 ∧ fS ≤ 4095 ∧ fS % 16 = 0 ∧ R1.lo ≤ -(fS : Int) + -160 - 48 ∧ 0 ≤ R1.hi ∧ R1.lo % 8 = 0 ∧
      R1.hi % 8 = 0 ∧
      fM = 96 ∧ R2.lo ≤ -(fM : Int) - 96 ∧ 0 ≤ R2.hi ∧ R2.lo % 8 = 0 ∧ R2.hi % 8 = 0 := by
  intro Z R1 R2
  show fS = 48 ∧ fS ≤ 4095 ∧ fS % 16 = 0 ∧ -D1 ≤ -(fS : Int) + -160 - 48 ∧ (0 : Int) ≤ 0 ∧ (-D1) % 8 = 0 ∧
      (0 : Int) % 8 = 0 ∧ fM = 96 ∧ -D2 ≤ -(fM : Int) - 96 ∧ (0 : Int) ≤ 0 ∧ (-D2) % 8 = 0 ∧ (0 : Int) % 8 = 0
  obtain ⟨hrS, -, -, hDS, hrM, -, -, hDM, -, -, -, -, -, -, hD1, -, hD2, -⟩ := hB
  obtain ⟨hS, hM⟩ := hello1_rowsA
  rw [hrS] at hS
  rw [hrM] at hM
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hS hM
  obtain ⟨rfl, rfl⟩ := hS
  obtain ⟨rfl, rfl⟩ := hM
  omega

/-- **`hello1`'s bounds exist** (`stackBounds2A` at `hello1o`, at any
layout and configuration with `CfgNeedOkA` whose placement check passes)
and fit its runtime calls (`hello1_bounds2A`). -/
theorem hello1_bounds2A_exists {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    (hcfg : Spike.Lib.LowerA64.CfgNeedOkA pcfg = true) (Lr : Spike.Lib.A64.Rt.RuntimeLayout) :
    ∃ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A SccCertificate.config P1A Lr L D1 D2 lS lM fS nS fM nM ∧ fS = 48 ∧ fM = 96 ∧
      ∀ v : BitVec 64,
        ((swR v (-L) 0).callee (-(Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1A)).Z.toInt)
          (-D1) 0).lo ≤ -(fS : Int) + -160 - 48 ∧
        ((swR v (-L) 0).callee (-(Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 P1A)).Z.toInt)
          (-D2) 0).lo ≤ -(fM : Int) - 96 := by
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ :=
    stackBounds2A h Spike.Lib.LowerNode.hello1o_accepted2 (by decide) hcfg Lr
  have H := hello1_bounds2A hB 0
  exact ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB, H.1, H.2.2.2.2.2.2.2.1, fun v =>
    ⟨(hello1_bounds2A hB v).2.2.2.1, (hello1_bounds2A hB v).2.2.2.2.2.2.2.2.1⟩⟩

/-- info: 'Spike.Test.A64Hello1Bounds.hello1_rowsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_rowsA

/-- info: 'Spike.Test.A64Hello1Bounds.hello1_bounds2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_bounds2A

/--
info: 'Spike.Test.A64Hello1Bounds.hello1_bounds2A_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hello1_bounds2A_exists

end Spike.Test.A64Hello1Bounds
