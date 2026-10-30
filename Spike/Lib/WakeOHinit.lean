/-
**`WakeO.OPrem.hinit` at `wakeD`** (AArch64): the load's
relation by `WakePreAsm.wake_init` at the runtime's layout
`L := RuntimeLayout.ofPlaceW hp i`, at an entry `E` clear of it:

- `hH0_W`: nothing held at the loaded thread (`HeldOk2 … []`): its private
  memory is the entry stack (`Entry.stackMem`), off the stack pool holding
  both takes' ranges;
- `hinit_W`: `OPrem.hinit`, by `WakeLoadT.wake_initT` at `wakeD`'s
  `L0T`/`ls0T` (main's `ThreadId` box at `tcb0`; `8 ≤ pinned.size` from
  `hpin2` and `pinA_toNat_ofPlaceW`). No static labels (`hstat`), the wide
  program (`wideIn_of_placeW`), the start's heap use `0` (heapbox: main's
  `ThreadId` box is discounted; decided), the owned words at the load
  (`WakeOInit.hown0_W`, `scc_rt_nthreads` by `NtZ`), `MemInv gW` at the
  load (`memInv_fixG_load`, `WakeG.memInv_wakeG`), the arena's
  (`ArenaW.arOf_sub`, `arOf_al`, `arOf_z0`, `arOf_c0`, given `CtrZ`).
  Open: the start in `inv0` (`hst`, `H0Stmt` `Start ⊆ inv0`).
-/
import Spike.Lib.WakeOInit
import Spike.Lib.WakeOD
import Spike.Lib.WakeOSide
import Spike.Lib.Rt.A64ArenaOfPlaceW

namespace Spike.Lib.WakeOHinit

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- A range in the stack pool is off the entry stack's private memory. -/
theorem unowned_stack {E : Entry} (hE : E.clear (Ly).Λ = true) {r : Range} (hr : r.Sub (Ly).Λ.stackPool)
    (hw : r.lo + r.size ≤ 2 ^ 64) (s : State) (hs : s.st.1.dmem = E.stackMem) : Unowned r s := by
  intro a ha hm
  rw [hs, Spike.Lib.DmemPriv.mem_stackMem (Entry.clear_disjoint hE).1] at hm
  have hd := (Entry.clear_disjoint hE).2 _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.stackPool ∈ (Ly).Λ.regions)
  have ha' : (BitVec.ofNat 64 a).toNat = a := by
    simp only [Range.contains] at ha; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [ha'] at hm
  obtain ⟨h1, h2⟩ := hr
  simp only [Range.contains, Range.Disjoint] at ha hm hd
  omega

/-- **`wake_init`'s `hH0`**: nothing held at the loaded thread. -/
theorem hH0_W {E : Entry} (hE : E.clear (Ly).Λ = true) (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) :
    HeldOk2 (Ly).Λ (WakeOSide.r0W hp i) (WakeOSide.r1W hp i)
      (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata)) [] := by
  obtain ⟨hs0, hs1, -, -, -, hw0, hw1⟩ := WakeOSide.ranges_W hp i hsub1
  exact .inl ⟨rfl, unowned_stack hp i hE hs0 hw0 _ rfl, unowned_stack hp i hE hs1 hw1 _ rfl⟩

/-- **`OPrem.hinit` at `wakeD`** (see the module doc). -/
theorem hinit_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : WakeOInit.NtZ Λ0 o = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (arch : WeakMem.Arch) {E : Entry} (hE : E.clear (Ly).Λ = true) (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isaLSE2) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    /- OPEN: the start in `inv0` -/
    (hst : inv0 (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨Spike.Lib.WakePreAsm.wakeTh0.term, Spike.Lib.WakePreAsm.wakeTh0.env, none⟩
      Spike.Lib.WakePreAsm.wakeTh0.stack) :
    let D := WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1
    ∀ d : Cfg, (target (kernel 1) E).load SccCertificate.asm (Ly).Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch wakeSrc) wakeSrc D.G D.own (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1)
          (HeldOk2 (Ly).Λ D.r0 D.r1) ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ) D.ar d s0 := by
  intro D
  have hpz : 8 ≤ (Ly).Λ.pinned.size := by
    have := PlaceW.pinA_toNat_ofPlaceW hp i; omega
  refine Spike.Lib.WakeLoadT.wake_initT (lsize := ls0) hpa hd (WakeOSide.hwf_W hp i) hpz
    (PlaceW.wideIn_of_placeW hp) (by decide) (.inl ⟨rfl, rfl, hst⟩)
    (hH0_W hp i hE hsub1) (fun t0 hl => ⟨WakeOInit.hown0_W hp i hpa hwp hlo (WakeOInit.hnt_of hp i hnz) E t0 hl,
      ?_, ?_, ?_⟩) hstat
    (Spike.Lib.A64.Rt.ArenaW.arOf_sub (PlaceW.link i hp)) (Spike.Lib.A64.Rt.ArenaW.arOf_al (PlaceW.link i hp))
  all_goals
    have he : Scc.Sem.A64.loadParsed (Scc.Sem.A64.kernel 1) E (Ly).Λ o.prog o.secs = _ :=
      Scc.Cert.Link.A64.loadParsed_of_loadOk (H := Scc.Sem.A64.kernel 1) (PlaceW.loadOk_link_of_placeW i hp) hE
    rw [he] at hl
    cases hl
  · exact Spike.Lib.WakeG.memInv_wakeG (Scc.Sem.memInv_fixG_load rfl rfl)
  · exact fun a ha => Spike.Lib.A64.Rt.ArenaW.arOf_z0 (PlaceW.link i hp) hc rfl ha
  · exact Spike.Lib.A64.Rt.ArenaW.arOf_c0 (PlaceW.link i hp) hc rfl

end Place

end Spike.Lib.WakeOHinit

/-- info: 'Spike.Lib.WakeOHinit.hinit_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOHinit.hinit_W
