/-
**`HrdS.hrd_WSHF`'s source and frame facts at the root** (AArch64): at the root's layout
`ofPlaceW hp (C0S.immsH Λ0 i0)`, its start's choices (`JS (Ly) 0#64 c0`, `c0S`'s environment):

- `hJ_JS`: every entry state of `scc_rt_main` after the switch is at the thread pointer `pinA + 8` and its `x0`
  represents main's id (`L0T` puts `mainTidLbl 2` at the TCB, `WakeHClW.hme_W`);
- `hme_c0S`: `me`'s one word in `c0S`'s environment is main's id;
- `hm_i0`, `hm_iRd`: `m`'s immediate `2` at `rodata`'s allocation `eB` at any certificate table with it, at
  `ImmsRd.iRd` (`helloImm_t2 = eB`);
- `hun_FS`: the limit word unmapped in private memory under the switch's frame condition `FS`;
- `j0_of_mNC`: non-vacuity, `wc_rodata`'s entry invariant inhabited at every caller's state at `mNC`.
-/
import Spike.Lib.A64HelloHrdS
import Spike.Lib.A64HelloImmsRd
import Spike.Lib.A64WakeHClW

namespace Spike.Lib.A64.HelloPh.HrdR

open CoreLang CoreTerm TermRun
open Scc.Sem (ValRep wordAddr)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **`me`'s one word in `c0S`'s environment is main's id.** -/
theorem hme_c0S : ∀ ty ws, lookupE Spike.Lib.A64.HelloPh.C0S.c0S.env "me" = some (ty, ws) →
    ws = [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)] := by
  intro ty ws h
  simp [Spike.Lib.A64.HelloPh.C0S.c0S_env, lookupE] at h
  exact h.2.symm

/-- **`helloImms` keeps `m`'s word `2` at `rodata`'s allocation** (`helloImm_t2 = eB`). -/
theorem helloImms_eB : SccCode.helloImms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2 := by
  show SccCode.helloImms SccCode.helloImm_t2 "m" 0 = some 2
  simp [SccCode.helloImms]

/-- `rodata`'s allocation is not the setup start's term. -/
theorem eB_ne_setup : Spike.Lib.HelloRodataSrc.eB ≠ Scc.Sem.SrcSem.setupTerm := by
  simp [Spike.Lib.HelloRodataSrc.eB, Scc.Sem.SrcSem.setupTerm]

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's layout at the certificate's table `i0`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0)

/-- **`m`'s immediate at `rodata`'s allocation at the root's layout**, given it in the certificate's table. -/
theorem hm_i0 (hi0 : i0 Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2) :
    (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2 := by
  show Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0 Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2
  simp only [Spike.Lib.A64.HelloPh.C0S.immsH, eB_ne_setup, false_and, ite_false]
  exact hi0

/-- **`m`'s immediate at `rodata`'s allocation at `ImmsRd.iRd`.** -/
theorem hm_iRd :
    (RuntimeLayout.ofPlaceW hpw (Spike.Lib.A64.HelloPh.ImmsRd.iRd Λ0)).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 =
      some 2 :=
  hm_i0 hpw _ (Spike.Lib.A64.HelloPh.ImmsRd.i0Rd_helloImms helloImms_eB)

/-- **`scc_rt_main`'s entry states after the switch**: at the thread pointer `pinA + 8`, `x0` main's id's
representation at `L0T`. -/
theorem hJ_JS {c0 : Spike.Lib.Ctl} : ∀ σ c, JS (Ly) 0#64 c0 σ c →
    σ.regs.TPIDR_EL0 = UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) ∧
      ValRep (L0T (Ly).Λ) (cst (.loc ⟨mainTidLbl 2, 0⟩ 0)).val σ.regs.X0.toBitVec.toNat := by
  rintro σ c ⟨⟨-, -, ht⟩, hx⟩
  refine ⟨ht, by decide, ((Ly).pinA + 8#64).toNat, ?_, ?_⟩
  · simp [wordAddr, Spike.Lib.WakeHClW.hme_W hpw _]
  · rw [hx]
    show (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64).toNat = ((Ly).pinA + 8#64).toNat + 0
    rw [Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero, Nat.add_zero]

end Root

/-- **The limit word is unmapped in private memory under the switch's frame condition.** -/
theorem hun_FS {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw : Int} {k0 v : BitVec 64} :
    ∀ m, FS L rS Lsw k0 v m →
      Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA L.lab +
        0#64 + 8#64))) 8 = none :=
  fun _ h => h.2.1.2

/-- **Non-vacuity of `hrd_WSHF`'s placement**: at every caller's state `σC` at `mNC` (every state the segment
`MainPreS.main_call_segW` reaches at `wc_rodata`'s call), `wc_rodata`'s entry invariant `mRdJ0 (rdJH lab J) σC`
holds at the entered state at `rodata`'s allocation, so `HrdS.rdPreW_frS'` takes its `FrP` branch there. -/
theorem j0_of_mNC {lab : Label → Int64} {J : FAS → Spike.Lib.Ctl → Prop} {σC : FAS} {c' : Spike.Lib.Ctl}
    (h : (Spike.Lib.A64.Flow.Hello1.mNC lab J).J σC c') :
    Spike.Lib.A64.Flow.Hello1.mRdJ0 (Spike.Lib.A64.HelloPh.StartWcS.rdJH lab J) σC
      (Spike.Lib.A64.Flow.enter (-80) σC) Spike.Lib.HelloRodataSrc.rdCN :=
  ⟨rfl, rfl, c', h⟩

end Spike.Lib.A64.HelloPh.HrdR

/-- info: 'Spike.Lib.A64.HelloPh.HrdR.hJ_JS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdR.hJ_JS

/-- info: 'Spike.Lib.A64.HelloPh.HrdR.hm_iRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HrdR.hm_iRd
