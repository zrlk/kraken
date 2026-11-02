/-
**hello.w on x86-64: `HMainRH`'s instance globals at a placed output** (the twin of
`Spike/Lib/HelloMainG.lean`): `X64HelloMainHRI.hMainRH_ofI`'s `hprog`, `hw`, `hpv`, `htop` at a placed output
`L := RuntimeLayout.ofPlaceWX hp i`.

- `hw_IH`: the placed executable is in the wide fragment, from `PlaceWX`'s `wideIn` check
  (`PlaceWX.wideIn_of_placeWX`, `wideSt_threadAt`).
- `hprog_IH`: `o.prog = helloCells` from the loader's two parses of the certificate.
- `htop_IH`: the child's ranges `r1` in the stack pool end in the address space.
- `hpv_IH`, `pre1T_privH`: `hpv` at `R1 ∧ VPriv L.Λ E` (`X64WakePrivR`), the relation hello's `Pre1T`
  strengthens to for a placed listing.

## Differences from the AArch64 version

- The loader's parse is `Scc.Sem.X64.cellsOf asm = some …` (AArch64: `textProgram asm = .ok …`), and the
  listing `SccCode.helloCells` (AArch64: `helloProg`); `pre1T_privH`'s `wideIn` is over the cells'
  directives.
- `htop_IH` is proved inline from the layout's well-formedness (AArch64: `WakeMainInst.htop_I`, which has no
  x86-64 twin).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `helloMI`, `hMi_IH`,
  `hMainRH_ofG`.
-/
import Spike.Lib.X64HelloMainHRI
import Spike.Lib.X64WakePrivR

namespace Spike.Lib.X64HelloMainG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64WakePreTi (Pre1T)
open Spike.Lib.X64WakePrivR (VPriv)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {r1 : ι → Range}
  {asm : Scc.Sem.X64.Asm} {E : Entry}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`hw`: the placed executable is in the wide fragment** (`PlaceWX`'s `wideIn` check at the canonical
thread). -/
theorem hw_IH : Scc.Cert.WideX64.ExeWide (Ly).exe :=
  (Scc.Cert.WideX64.wideSt_threadAt (PlaceWX.wideIn_of_placeWX hp) Scc.Sem.Entry.linux _ _).2

/-- **`hprog`** from the loader's two parses of the certificate. -/
theorem hprog_IH (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells) :
    o.prog = SccCode.helloCells :=
  Option.some.inj (hpa.symm.trans hhp)

/-- **`htop`**: the child's ranges in the stack pool end in the address space. -/
theorem htop_IH (hsub1 : ∀ w, (r1 w).Sub (Ly).Λ.stackPool) : ∀ w, (r1 w).lo + (r1 w).size ≤ 2 ^ 64 :=
  fun w => Nat.le_trans (hsub1 w).2
    (((PlaceWX.wf_link_of_placeWX i hp : (Ly).Λ.WF)).inSpace (Ly).Λ.stackPool
      (by simp only [Scc.Sem.Layout.regions, List.mem_cons]; exact .inr (.inr (.inr (.inl rfl))))).2

/-- **`hpv`** at `R1 ∧ VPriv`. -/
theorem hpv_IH : ∀ d s, (R1 d s ∧ VPriv (Ly).Λ E d) →
    ∃ (Ent : Entry) (P : State → Prop), Ent.clear (Ly).Λ = true ∧ Spike.Lib.DmemPriv.PrivInv abi P (Ly).Λ Ent d :=
  fun _ _ h => X64WakePrivR.priv_of_R1 h

/-- **hello's `Pre1T` strengthened by `VPriv`** for a placed certificate (the text's cells are the placed
listing, in the wide fragment; `X64WakePrivR.Pre1T.priv`'s twin at `helloSrc`). -/
theorem pre1T_privH {Ab Ac : State → Prop} {B : Budget} (hpa : cellsOf asm = some o.prog)
    (O : Pre1T arch (Ly).Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch (Ly).Λ B asm E (fun d s => R1 d s ∧ VPriv (Ly).Λ E d) Ab Ac helloSrc :=
  have hw : ∀ cells, cellsOf asm = some cells → Scc.Cert.WideX64.wideIn (cells.map (·.1)) = true := by
    intro cells h
    rw [hpa] at h
    cases h
    exact PlaceWX.wideIn_of_placeWX hp
  Spike.Lib.X64WakePreInv.Pre1T.inv O (fun d _ => VPriv (Ly).Λ E d)
    (fun _ _ hd _ _ => ⟨X64WakePrivR.clear_of_load hd, (Spike.Lib.X64WakeRunInv.runInv_load hw hd).1⟩)
    (fun _ _ _ _ _ _ _ hV _ hs _ _ => ⟨hV.1, Spike.Lib.X64DmemPriv.privInv_step hV.2 hs⟩)

end Inst

end Spike.Lib.X64HelloMainG

/-- info: 'Spike.Lib.X64HelloMainG.hw_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainG.hw_IH

/-- info: 'Spike.Lib.X64HelloMainG.hprog_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainG.hprog_IH

/-- info: 'Spike.Lib.X64HelloMainG.htop_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainG.htop_IH

/-- info: 'Spike.Lib.X64HelloMainG.hpv_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainG.hpv_IH

/-- info: 'Spike.Lib.X64HelloMainG.pre1T_privH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainG.pre1T_privH
