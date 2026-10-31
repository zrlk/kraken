/-
**wake's clone facts from `h1`** (x86-64; the
`hpost` half of `Spike/Lib/A64WakeHClW.lean`): the premise `hpost` of
`X64WakeSpawnR.hpc_of` (main's state at the clone is `ClonePost`'s) from
the pre-spawn relation at main's `clone`.

At a `SpawnPrem`, main is at a system call that decodes to `clone`. A
fragment state off `Cl` at a system call is not at a `clone`
(`NodesA.sysOkXCT`), so the state is `Cl`, hence at the clone's pc. `inv0`
is never there, so the state is `inv1`'s and has `CloneInv`.

- `pc_of_clone`: a fragment state at a `clone` call is at the clone's pc,
  given `Cl` only there.
- `cloneInv_of_I2`: `CloneInv` at an `I2` state at a `clone` call (the
  `inv0` side off the clone's pc, the `inv1` side's clone clause).
- `cloneInv_of_spawnPrem`: the same at `PreJAH`'s witnesses, from a
  `SpawnPrem` under any relation below `R1O`.
- `hpost_of`: `hpc_of`'s `hpost` (main's state at the clone is
  `ClonePost`'s).
- At `wakeD` with the levels `W0W`/`W1W` and `h1`'s invariant `inv1W`
  (`X64WakeH1Inv`): `nodes_of` (`NodesA`, `TakeSiteS` from `OPrem`),
  `hpost_W` (`hpost` from `OPrem`: `inv0` off the clone by
  `X64.WakeWf.noClone_of` at `OPrem.h0`, `inv1W`'s clone clause by
  `X64.WakeH1Inv.cloneInv_of`), `hpc_W` (`hpc_of` with `hpost_W`) and
  `hpostC_W` (`X64WakeMainHRI.hMainR_I`'s `hpost`, at `Ctl.of s0`).
- `clonePost_ctl`: `ClonePost` holds at any control (it reads `c` only
  through its own `c = c0`).

**Where this differs from AArch64**:
- `wakeD` takes the levels and invariants as parameters. So `hpost_W` is
  stated at `W0W`, `W1W`, `inv1W` and any `inv0`; A64's `DH` fixes them.
- `CloneInv` also names `c`'s label `l`.
- The clone-argument and `hCl` halves of A64's module (`clone_args`,
  `hCl_of`, `hCl_W`) are not twinned here. `X64WakeHPre.hpre_of`'s `hCl`
  has its own x86-64 shape (`%r8`, `PreR.hcm`).
-/
import Spike.Lib.X64WakeHPre
import Spike.Lib.X64WakeH1Inv
import Spike.Lib.X64WakeX0
import Spike.Lib.X64WakeOPremW
import Spike.Lib.X64SFactsACH

namespace Spike.Lib.X64WakeHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (I2 NodesA)
open Spike.Lib.X64ConsumerS (TakeSiteS InvS OwnS)
open Spike.Lib.X64.Flow.WakeWc (clonePc CloneInv ClonePost)
open Spike.Lib.X64WakeSpawnR (ιR QG PreR)
open Spike.Lib.X64 (AS)

/-- **A fragment state at a `clone` call is at the clone's pc**, where `Cl`
marks only states there: off `Cl`, `NodesA.sysOkXCT` rules the call out. -/
theorem pc_of_clone {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS}
    {ab : Option (State → Prop)} {Cl : State → Prop} {L : RuntimeLayout}
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hT : TakeSiteS p μ I) (hCl : ∀ s, Cl s → pcOf s = clonePc L)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) : pcOf s = clonePc L := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT hI hs fun h => hne (hCl s h)
  rw [hcall] at hd
  cases hd
  exact hcl st tl rfl

/-- **`CloneInv` at an `I2` state at a `clone` call**: `inv0` is off the
clone's pc (`hnc0`), `inv1` has `CloneInv` there (`hcl1`). -/
theorem cloneInv_of_I2 {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)} {Cl : State → Prop}
    {L : RuntimeLayout} {endPc : Int64} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isa}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    (hN : NodesA Λ wakeSrc μ rd G own ar (I2 ar L0 ls0 inv0 inv1) ab Cl)
    (hT : TakeSiteS wakeSrc μ (I2 ar L0 ls0 inv0 inv1)) (hCl : ∀ s, Cl s → pcOf s = clonePc L)
    (hnc0 : ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePc L)
    (hcl1 : ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = clonePc L →
      CloneInv L endPc (X64ConsumerA.upd L0 l b) s c fs)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    CloneInv L endPc lbl s c fs := by
  have hpc := pc_of_clone hN hT hCl hI hs hcall
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, rfl, -, hi⟩
  · exact absurd hpc (hnc0 s c fs hi)
  · exact hcl1 l b n s c fs hi hpc

/-- **`ClonePost` does not read the control** beyond its own `c = c0`
(`wcNS`'s `JA`, `JS`): it holds at any control `c'`. -/
theorem clonePost_ctl {L : RuntimeLayout} {endPc : Int64} {J : AS → Ctl → Prop} {t : UInt64} {s : State}
    {c : Ctl} (c' : Ctl) (h : ClonePost L endPc J t s c) : ClonePost L endPc J t s c' := by
  obtain ⟨R, F₂, σC, cA, m, fr, hfr, ⟨he, hend, hd, hpc, σ, hA, hF, ⟨⟨-, hJA⟩, hJL⟩, hJS⟩, hok,
    ⟨he', hend', hd', hpc', σ', hA', hF', -, hS⟩, hb, hsp, htp, hσ⟩ := h
  exact ⟨R, F₂, σC, cA, m, fr, hfr, ⟨he, hend, hd, hpc, σ, hA, hF, ⟨⟨rfl, hJA⟩, hJL⟩, hJS⟩, hok,
    ⟨he', hend', hd', hpc', σ', hA', hF', rfl, hS⟩, hb, hsp, htp, hσ⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

variable {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
  {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {D : X64WakeO.OData} {μ' : Marks}

/-- **`CloneInv` at `PreJAH`'s witnesses** from a `SpawnPrem` under a
relation below `R1O` (`hR1`): main's thread, its source thread with empty
stack's control in `I2`, main at the clone's pc with `CloneInv`. -/
theorem cloneInv_of_spawnPrem (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (X64WakeAssemblyR.endR hp i) (X64ConsumerA.upd D.L0 l b) s c fs)
    {d : Cfg} {s : TermRun.Cfg} {th : Thread isa} {stack tls : Nat} {r : BitVec 64}
    (hP : SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r) :
    ∃ (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (hd : Option (Nat × TermRun.Word)),
      d.1.threads = #[th] ∧ s.ths = #[th0] ∧
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧
      CloneInv (Ly) (X64WakeAssemblyR.endR hp i) lbl th.st ⟨th0.term, th0.env, hd⟩ th0.stack := by
  obtain ⟨h1, -, h3, h4, -, h6, h7, -⟩ := id hP
  obtain ⟨⟨⟨⟨hRS, -⟩, -⟩, -⟩, -⟩ := hR1 _ _ h1
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at h6; cases h6
  obtain ⟨thm, th0, -, lbl, lsize, -, -, -, hd, hth, -, -, -, -, -, hs, -, -, hJ, -⟩ := hPre
  obtain rfl : thm = th := by rw [hth] at h3; exact Option.some.inj h3
  exact ⟨th0, lbl, lsize, hd, hth, hs, hJ, cloneInv_of_I2 hN hT hCl hnc0 hcl1 hJ h4 h7⟩

/-- **`hpc_of`'s `hpost`**: main's state at the clone is `ClonePost`'s
(`cloneInv_of_spawnPrem`'s `CloneInv`). -/
theorem hpost_of (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (X64WakeAssemblyR.endR hp i) (X64ConsumerA.upd D.L0 l b) s c fs) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, ClonePost (Ly) (X64WakeAssemblyR.endR hp i) J t th.st c := by
  intro d s th stack tls r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ _
  obtain ⟨_, _, _, _, -, -, -, hci⟩ := cloneInv_of_spawnPrem hp i hR1 hN hT hCl hnc0 hcl1 hP
  obtain ⟨-, J, t, -, hcp, -⟩ := hci
  exact ⟨_, J, t, hcp⟩

variable {B : Budget} {Ab Ac : State → Prop} (cT : Loc) (Dt : State → Prop) (ls0 : Lsize) (Ctx : FragS isa)
  (frM : TermRun.Frame) (inv0 : FragS isa)

set_option hygiene false in
/-- `wakeD` at the levels `W0W`, `W1W` and `h1`'s invariant `inv1W`. -/
local notation "DH" =>
  X64.WakeOD.wakeD hp i E cT Dt ls0 (X64.WakeOPremW.W0W asm hp i E Dt Ctx ls0 frM) inv0
    (X64.WakeOPremW.W1W asm hp i E Dt Ctx ls0) (X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0)

/-- **`NodesA` and `TakeSiteS` at `wakeD`** from `OPrem` there
(`inst_of_segWA2CH2`). -/
theorem nodes_of (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    NodesA (Ly).Λ wakeSrc ((target (kernel 2) E).marks asm (Ly).Λ) (DH).rd (DH).G (DH).own (DH).ar
        (I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1) none (DH).Cl ∧
      TakeSiteS wakeSrc ((target (kernel 2) E).marks asm (Ly).Λ) (I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1) :=
  let h := X64ConsumerA.inst_of_segWA2CH2 hO.h1 hO.h0 hO.ha hO.hW0 hO.hW1 hO.hsplit hO.hs0 hO.hs1 hO.hz0 hO.hz1
    hO.hro hO.hd hO.hw0 hO.hw1
  ⟨h.1, h.2.1.toTakeSiteS⟩

/-- **`hpost` at `wakeD` with `inv1W`**, from `OPrem` there. -/
theorem hpost_W (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, ClonePost (Ly) (X64WakeAssemblyR.endR hp i) J t th.st c :=
  hpost_of hp i hR1 (nodes_of hp i cT Dt ls0 Ctx frM inv0 hO).1 (nodes_of hp i cT Dt ls0 Ctx frM inv0 hO).2
    (fun _ h => h.1) (X64.WakeWf.noClone_of hO.h0)
    (fun l b n => X64.WakeH1Inv.cloneInv_of asm hp i E cT Dt Ctx ls0 l b n)

/-- **main's segment end at every `PreR`** at `wakeD` with `inv1W`
(`X64WakeSpawnR.hpc_of` with `hpost_W`): X64-endR closed down to `OPrem`. -/
theorem hpc_W (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA fp ra tp, X64WakeMainHRD.MainSeg (Ly) (X64WakeAssemblyR.endR hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧
        ∀ k, -64 ≤ k → k < 16 → (Ly).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -64, 16⟩ : Region).addr k).toNat :=
  X64WakeSpawnR.hpc_of hp i (hpost_W hp i cT Dt ls0 Ctx frM inv0 hR1 hO)

/-- **`X64WakeMainHRI.hMainR_I`'s `hpost`** at `wakeD` with `inv1W`:
`hpost_W` at main's control after the spawn, `Ctl.of s0` (`clonePost_ctl`). -/
theorem hpostC_W (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ J t, ClonePost (Ly) (X64WakeAssemblyR.endR hp i) J t th.st (Ctl.of s0) := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨_, J, t, h⟩ := hpost_W hp i cT Dt ls0 Ctx frM inv0 hR1 hO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hP hrun hR
  exact ⟨J, t, clonePost_ctl _ h⟩

end Inst

end Spike.Lib.X64WakeHClW

/-- info: 'Spike.Lib.X64WakeHClW.pc_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.pc_of_clone

/-- info: 'Spike.Lib.X64WakeHClW.cloneInv_of_I2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.cloneInv_of_I2

/-- info: 'Spike.Lib.X64WakeHClW.hpost_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.hpost_W

/-- info: 'Spike.Lib.X64WakeHClW.clonePost_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.clonePost_ctl

/-- info: 'Spike.Lib.X64WakeHClW.hpostC_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.hpostC_W

/-- info: 'Spike.Lib.X64WakeHClW.hpc_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClW.hpc_W
