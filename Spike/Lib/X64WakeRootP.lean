/-
**The root's take-site frame `P := Pz rS0` holds at the loaded thread**
(x86-64; the non-vacuity of the P producers, `Spike/Lib/X64WakeStartTiP.lean`,
`Spike/Lib/X64WakeStartWfP.lean`, `Rt.startEF_segWA`): the frame `P` that the
root threads from `_start` to the first take's site, where `X0W` asks
`¬ StackM r0` (`Pz.pz_not_stackM`). It holds at the loaded thread, whose
private memory is the entry stack's, the stack pool off it; it is kept by
every frame of the entry region (the pool is off the entry stack); and at
the site it gives `X0W`'s clause from the site's range.

- `pz_rS0_stackMem`, `pz_rS0_load`: `Pz rS0` at the entry stack's private
  memory and at the loaded thread (`threadAt`).
- `pz_rS0_fstable`: `FStable (entryR E) (Pz rS0)`, `startEF_segWA`'s `hP`.
- `x0W_sitePz`: `X0W` at the take site from its range and `Pz r0`, the
  site off the clone's pc (`hc`): the P twins' `hXs` at `P := Pz r0`.
- `r0Of_rS0`: `r0Of L.lab` is `rS0 L`.

x86-64 twin of AArch64's `StartH0R.pz_rS0_load` (`Spike/Lib/A64WakeStartH0R.lean`)
and `StartH0Ti`'s site clause.

**Unlike AArch64**: the loaded thread is `Scc.Sem.X64.threadAt`, whose
private memory is `E.stackMem` by definition, so `pz_rS0_load` needs only
the layout's entry clearance (`E.clear L.Λ`; A64 goes through
`WakeOHinit.unowned_stack` at `ofPlaceW`), at any `RuntimeLayout`; `rS0`
is `Rt.rS0 L` (`(L.stacksA + 0).toNat`, 16 KiB) and `r0Of L.lab` its
label form.
-/
import Spike.Lib.X64WakeStartWfP
import Spike.Lib.X64WakePz
import Spike.Lib.X64WakeTi2HatG

namespace Spike.Lib.X64.WakePh.RootP

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf abi codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rS0 rS0_sub pool_clear outS_of_sub)
open Spike.Lib.X64Consumer (Pz)

variable {L : RuntimeLayout}

/-- **`Pz rS0` at the entry stack's private memory**: the first stack's
first word, in the pool, is clear of the entry stack. -/
theorem pz_rS0_stackMem {E : Scc.Sem.Entry} (hE : E.clear L.Λ = true) {m : MachineData}
    (hm : m.dmem = E.stackMem) : Pz (rS0 L) m := by
  have hfit := (Scc.Sem.Entry.clear_disjoint hE).1
  have hb := pool_clear L hE
  have hs := rS0_sub L
  have hpf := L.pool_fit
  have hn : (BitVec.ofNat 64 (rS0 L).lo).toNat = (rS0 L).lo := by
    rw [BitVec.toNat_ofNat]; unfold RuntimeLayout.pool at hs; obtain ⟨-, h⟩ := hs; omega
  unfold Pz; rw [hm]
  refine Spike.Lib.X64.Rt.stackMem_loadInt hfit ?_
  unfold Spike.Lib.X64.Rt.Clear; rw [hn]
  unfold RuntimeLayout.pool at hs
  have hlo : (rS0 L).lo = (L.stacksA + 0#64).toNat := rfl
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hb hs
  omega

/-- **`Pz rS0` at the loaded thread** (`threadAt`, its private memory the
entry stack's). -/
theorem pz_rS0_load {E : Scc.Sem.Entry} (hE : E.clear L.Λ = true) (base : Nat)
    (cells : List (Directive × Nat)) (syms : List (String × Nat)) :
    Pz (rS0 L) (Scc.Sem.X64.threadAt E base cells syms).st.1 :=
  pz_rS0_stackMem hE rfl

/-- **`Pz rS0` is kept by the entry region's frames** (`startEF_segWA`'s
`hP` at `R := entryR E`): the first stack's first word is clear of the
entry stack's region. -/
theorem pz_rS0_fstable {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) :
    Spike.Lib.X64.FStable (entryR E) (Pz (rS0 L)) := by
  intro m m' h hd
  have hal : (rS0 L).lo % 8 = 0 := by
    have := L.stacks_al; show (L.stacksA + 0#64).toNat % 8 = 0; rw [BitVec.add_zero]; omega
  have hs := rS0_sub L
  have hpf := L.pool_fit
  have hlt : (rS0 L).lo + 8 ≤ 2 ^ 64 := by
    unfold RuntimeLayout.pool at hs; obtain ⟨-, h⟩ := hs; omega
  have hn : (BitVec.ofNat 64 (rS0 L).lo).toNat = (rS0 L).lo := by rw [BitVec.toNat_ofNat]; omega
  have ho := outS_of_sub L hE hs (rS0 L).lo hal ⟨Nat.le_refl _, by show _ < _ + 16384; omega⟩
    ⟨by omega, by show _ < _ + 16384; omega⟩
  unfold Pz
  rw [hd _ (by rw [hn]; exact hlt) (by rw [hn]; exact ho)]
  exact h

/-- **`X0W` at the take site from `Pz r0`**: the site's range `r0` (`hr`),
`¬ StackM r0` from its first word unmapped (`Pz.pz_not_stackM`), the site
off the clone's pc (`hc`), at any take pc `a`. -/
theorem x0W_sitePz {a : Int64} (hc : (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat ≠
      Spike.Lib.X64.Flow.WakeWc.clonePc L) :
    ∀ s, pcOf s = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.X64.Rt.Ti2.r0Of L.lab →
      Pz (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s.st.1 → Spike.Lib.X64.WakeWf.X0W L a s := by
  intro s hp hr hz
  have hal : (Spike.Lib.X64.Rt.Ti2.r0Of L.lab).lo % 8 = 0 := by
    rw [(Spike.Lib.X64.Rt.Ti2.r0Of_eq L.lab).1, L.lab_stacks]; have := L.stacks_al; omega
  exact ⟨hp ▸ hc, fun _ => ⟨hr, Spike.Lib.X64.WakePh.Pz.pz_not_stackM hal
    (by rw [(Spike.Lib.X64.Rt.Ti2.r0Of_eq L.lab).2]; decide) hz⟩⟩

/-- **`r0Of` is `rS0`** at the layout's labels. -/
theorem r0Of_rS0 : Spike.Lib.X64.Rt.Ti2.r0Of L.lab = rS0 L := by
  unfold Spike.Lib.X64.Rt.Ti2.r0Of; rw [L.lab_stacks]

end Spike.Lib.X64.WakePh.RootP

/-- info: 'Spike.Lib.X64.WakePh.RootP.pz_rS0_stackMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootP.pz_rS0_stackMem

/-- info: 'Spike.Lib.X64.WakePh.RootP.pz_rS0_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootP.pz_rS0_load

/-- info: 'Spike.Lib.X64.WakePh.RootP.pz_rS0_fstable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootP.pz_rS0_fstable

/-- info: 'Spike.Lib.X64.WakePh.RootP.x0W_sitePz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootP.x0W_sitePz

/-- info: 'Spike.Lib.X64.WakePh.RootP.r0Of_rS0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootP.r0Of_rS0
