/-
**The start's `hrd`'s source and frame facts at the root** (x86-64; the twin of the live part of
`Spike/Lib/A64HelloHrdR.lean`): at the root's layout `ofPlaceWX hpw (HelloImms.immsH Λ0 i0)`, its start's choices
(`JS (Ly) 0#64 c0`, `c0S`'s environment):

- `hJ_JS`: every entry state of `scc_rt_main` after the switch is at the thread pointer `tpOf (tcbS Ly)` and its
  `%rdi` represents main's id (`L0T` puts `mainTidLbl 2` at the TCB `pinA + 8`);
- `hme_c0S`: `me`'s one word in `c0S`'s environment is main's id;
- `hun_FS`: the limit word unmapped in private memory under the switch's frame condition `FS`.

## Differences from the AArch64 version

- The thread pointer is `%fs`'s base at `tpOf (tcbS Ly)` (AArch64: `TPIDR_EL0` at `pinA + 8`) and main's id is
  passed in `%rdi` (AArch64: `x0`); `L0T`'s TCB entry is read off its definition (as `Box.hmt_H`; AArch64:
  wake's `WakeHClW.hme_W`).
- `FS`'s limit word is at `limA (tpOf (tcbS L))`, the conjunct `h.1.2.1.2` (AArch64 `h.2.1.2`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `helloImms_eB`, `eB_ne_setup`,
  `hm_i0`, `hm_iRd`, `j0_of_mNC`.
-/
import Spike.Lib.X64HelloHrdS
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64HelloImms
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.HelloPh.HrdR

open CoreLang CoreTerm TermRun
open Scc.Sem (ValRep wordAddr)
open Spike.Lib.X64WakeT1 (mainTidLbl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.Flow.Ret0 (tpOf limA)
open Spike.Lib.X64.WakePh.MainGlue (FS JS tcbS)

/-- **`me`'s one word in `c0S`'s environment is main's id.** -/
theorem hme_c0S : ∀ ty ws, lookupE Spike.Lib.X64.HelloPh.C0S.c0S.env "me" = some (ty, ws) →
    ws = [cst (.loc ⟨mainTidLbl 2, 0⟩ 0)] := by
  intro ty ws h
  simp [Spike.Lib.X64.HelloPh.C0S.c0S_env, lookupE] at h
  exact h.2.symm

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's layout at the certificate's table `i0`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.immsH Λ0 i0)

/-- **`scc_rt_main`'s entry states after the switch**: at the thread pointer `tpOf (tcbS Ly)`, `%rdi` main's id's
representation at `L0T`. -/
theorem hJ_JS {c0 : Spike.Lib.Ctl} : ∀ σ c, JS (Ly) 0#64 c0 σ c →
    σ.regs.fsBase = tpOf (tcbS (Ly)) ∧
      ValRep (L0T (Ly).Λ) (cst (.loc ⟨mainTidLbl 2, 0⟩ 0)).val σ.regs.rdi.toBitVec.toNat := by
  rintro σ c ⟨⟨-, -, ht⟩, hx⟩
  have hp0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw (Spike.Lib.X64.HelloImms.immsH Λ0 i0)
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have hme : L0T (Ly).Λ (mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
    simp only [L0T, Spike.Lib.X64ConsumerA.upd, ↓reduceIte, Spike.Lib.X64WakeLoadT.tcb0, Option.some.injEq]
    omega
  have hpin8 : (tcbS (Ly)).toNat = (Ly).pinA.toNat + 8 := by
    show (Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64).toNat = _
    rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨ht, by decide, (Ly).pinA.toNat + 8, ?_, ?_⟩
  · simp [wordAddr, hme]
  · rw [hx]
    show (UInt64.ofNat (tcbS (Ly)).toNat).toNat = (Ly).pinA.toNat + 8 + 0
    rw [UInt64.toNat_ofNat', hpin8]; omega

end Root

/-- **The limit word is unmapped in private memory under the switch's frame condition.** -/
theorem hun_FS {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw : Int} {k0 v : BitVec 64} :
    ∀ m, FS L rS Lsw k0 v m → Mem.loadInt m.dmem (limA (tpOf (tcbS L))) 8 = none :=
  fun _ h => h.1.2.1.2

end Spike.Lib.X64.HelloPh.HrdR

/-- info: 'Spike.Lib.X64.HelloPh.HrdR.hme_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdR.hme_c0S

/-- info: 'Spike.Lib.X64.HelloPh.HrdR.hJ_JS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdR.hJ_JS

/-- info: 'Spike.Lib.X64.HelloPh.HrdR.hun_FS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdR.hun_FS
