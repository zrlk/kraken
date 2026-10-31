/-
**`X64WakeO.OPrem.hinit` at `wakeD`** (x86-64): the load's relation by
`X64WakeLoadT.wake_initT` at the runtime's layout
`L := RuntimeLayout.ofPlaceWX hp i`, at an entry `E` clear of it:

- `unowned_stack`: a range in the stack pool is off the entry stack's
  private memory;
- `hH0_W`: nothing held at the loaded thread (`HeldOk2 … []`): its private
  memory is the entry stack (`Entry.stackMem`), off the stack pool holding
  both takes' ranges;
- `hinit_W`: `OPrem.hinit`, by `X64WakeLoadT.wake_initT` at `wakeD`'s
  `L0T`/`ls0T` (main's `ThreadId` box at `tcb0`; `8 ≤ pinned.size` from
  `hpin2` and `pinA_toNat_ofPlaceWX`). No static labels (`hstat`), the wide
  program (`wideIn_of_placeWX`), the start's heap use `0` (decided), the
  owned words at the load (`X64WakeOInit.hown0_W`, `scc_rt_nthreads` by
  `NtZ`), `MemInv gW` at the load (`memInv_fixG_load`,
  `WakeG.memInv_wakeG`), the arena's (`ArenaW.arOf_sub`, `arOf_al`,
  `arOf_z0`, `arOf_c0`, given `CtrZ`). Open: the start in `inv0` (`hst`).

x86-64 twin of `Spike/Lib/WakeOHinit.lean`. **Unlike AArch64**:
- the parse is `cellsOf asm = some o.prog`/`= some wakeCells` with the data
  sections and the label offsets (`hd`, `hoffs`; the load reads them);
- `wakeD` takes the levels and invariants as parameters (as A64), its `own`
  is `ownGXW` (`X64WakeOInit.ownGXW_lo`).
-/
import Spike.Lib.X64WakeOInit
import Spike.Lib.X64WakeOD
import Spike.Lib.X64WakeOSide
import Spike.Lib.X64WakeLoadT
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.X64PlaceW

namespace Spike.Lib.X64WakeOHinit

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCode (wakeCells)
open Spike.Lib (PlaceWX)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

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

/-- **`wake_initT`'s `hH0`**: nothing held at the loaded thread. -/
theorem hH0_W {E : Entry} (hE : E.clear (Ly).Λ = true) (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) :
    HeldOk2 (Ly).Λ (X64WakeOSide.r0W hp i) (X64WakeOSide.r1W hp i)
      (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata)) [] := by
  obtain ⟨hs0, hs1, -, -, -, hw0, hw1⟩ := X64WakeOSide.ranges_W hp i hsub1
  exact .inl ⟨rfl, unowned_stack hp i hE hs0 hw0 _ rfl, unowned_stack hp i hE hs1 hw1 _ rfl⟩

/-- **`OPrem.hinit` at `wakeD`** (see the module doc). -/
theorem hinit_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hnz : X64WakeOInit.NtZ Λ0 o = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (arch : WeakMem.Arch) {E : Entry} (hE : E.clear (Ly).Λ = true) (cT : Loc) (Dt : State → Prop) (ls0 : Lsize)
    (W0 inv0 : FragS isa) (W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    /- OPEN: the start in `inv0` -/
    (hst : inv0 (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
      Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    let D := X64.WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 W1 inv1
    ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch wakeSrc) wakeSrc D.G D.own (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1)
          (HeldOk2 (Ly).Λ D.r0 D.r1) ((target (kernel 2) E).marks asm (Ly).Λ) D.ar d s0 := by
  intro D
  have hpz : 8 ≤ (Ly).Λ.pinned.size := by
    have := PlaceWX.pinA_toNat_ofPlaceWX hp i; omega
  refine Spike.Lib.X64WakeLoadT.wake_initT (lsize := ls0) hpa hd (X64WakeOSide.hwf_W hp i) hpz
    (PlaceWX.wideIn_of_placeWX hp) (by decide) (.inl ⟨rfl, rfl, hst⟩)
    (hH0_W hp i hE hsub1) (fun t0 hl => ⟨X64WakeOInit.hown0_W hp i hpa hwp hlo (X64WakeOInit.hnt_of hp i hnz) E t0
      (hoffs ▸ hl), ?_, ?_, ?_⟩) hstat
    (Spike.Lib.X64.Rt.ArenaW.arOf_sub (PlaceWX.link i hp)) (Spike.Lib.X64.Rt.ArenaW.arOf_al (PlaceWX.link i hp))
  all_goals
    rw [hoffs] at hl
    have he : Scc.Sem.X64.loadParsed (Scc.Sem.X64.kernel 1) E (Ly).Λ o.prog o.secs o.labelOffs = _ :=
      Scc.Cert.Link.X64.loadParsed_of_loadOk (H := Scc.Sem.X64.kernel 1) (PlaceWX.loadOk_link_of_placeWX i hp) hE
    rw [he] at hl
    cases hl
  · exact Spike.Lib.WakeG.memInv_wakeG (Scc.Sem.memInv_fixG_load rfl rfl)
  · exact fun a ha => Spike.Lib.X64.Rt.ArenaW.arOf_z0 (PlaceWX.link i hp) hc rfl ha
  · exact Spike.Lib.X64.Rt.ArenaW.arOf_c0 (PlaceWX.link i hp) hc rfl

end Place

end Spike.Lib.X64WakeOHinit

/-- info: 'Spike.Lib.X64WakeOHinit.hinit_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOHinit.hinit_W
