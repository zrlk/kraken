/-
**`wc_main`'s placement up to the box's store** (x86-64, wake.w): every
control of `wc_main`'s nodes from its entry to `.x18`'s store is the start
control `c0` (with a hold from the allocator's add on), so they are placed
wherever `c0` is (`hpl0`, `StartPlace.wake_start_wc_place`'s premise); the
allocator's states are placed through its call context (`WcCtx` pins its
control to the caller's).

- `c0_wJ0`, `tp_wJ0`: `wc_main`'s entry invariant at `scc_rt_main`'s after
  the switch (`wJ0 (wNC L.lab (JS L k0 c0)).J σC`) pins the control to `c0`
  and the thread pointer to the first TCB.
- `blkW_q`, `nodeW_q`: a node whose controls satisfy a state-free fact.
- `wcPreW_pl`, `wcSp0W_pl`: `WcPreW` / `WcSp0W` inside the placement at any
  entry invariant whose controls are `c0`.
- `hplP_W`, `hplS_W`: at `wc_main`'s entry invariant (`WcWfS.wcPreW_WSO`'s /
  `wcSp0W_WSO`'s `hpl`).

x86-64 twin of `Spike/Lib/A64WakeWcPl.lean` (namespace
`Spike.Lib.X64.WakePh.WcPl`). **Where this differs from AArch64**: the start
control is any `c0` placed at any labels `lbl` (`hpl0`; A64 fixes `c0W` at
`L0T`, placed by `WakeImmsC0.placedSE_c0WW` at the root's immediate table),
so the statements are generic in the layout and need no region bounds; the
allocator's states are placed from its call context (`allocW_of_ctl`; A64
by `PlacedAlloc.allocW_placed_new` from `c0W`'s term and immediates);
`wc_main`'s entry invariant is `MainGlue`'s at `mainE0` (A64 `wJ0_wNC_JS`,
in `WcWfS`), the thread pointer `fsBase` (A64 `TPIDR_EL0`).
-/
import Spike.Lib.X64WakeWcWfS
import Spike.Lib.X64WakeMainL
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.WakePh.WcPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW holdCtr)
open Spike.Lib.X64.WakePh.MainGlue (JS tcbS)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W sN wN wcJ)

/-! ## `wc_main`'s entry at the start's invariant -/

section Entry

variable {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Ctl} {σC σ : Spike.Lib.X64.AS} {c : Ctl}

/-- **`wc_main`'s entry control is the start's** (`MainGlue`'s
`wJ0 (wNC L.lab (JS L k0 c0)).J σC`). -/
theorem c0_wJ0 (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c) : c = c0 := by
  obtain ⟨-, ⟨σe, ⟨⟨hc, -⟩, -⟩, -⟩, -⟩ := h
  exact hc

/-- **`wc_main`'s entry thread pointer is the first TCB's.** -/
theorem tp_wJ0 (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σ c) : σ.regs.fsBase = tpOf (tcbS L) := by
  obtain ⟨rfl, ⟨σe, ⟨⟨-, -, htp⟩, -⟩, -, -, -, -, hfs⟩, -⟩ := h
  show σC.regs.fsBase = _
  rw [hfs, htp]

end Entry

/-! ## Inside the placement -/

section Pl

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {Q : Spike.Lib.Frag isa}

/-- **A block whose controls satisfy a state-free fact `Q · c`.** -/
theorem blkW_q {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → ∀ s, Q s c) :
    BlkW Q (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
  exact ⟨h σ c hJ _, fun _ h => h⟩

/-- **A node whose controls satisfy a state-free fact `Q · c`.** -/
theorem nodeW_q {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, Q s c) : NodeW Q (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨h σ c hJ _, fun _ h => h⟩

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Ctl} (hpl0 : ∀ s, PlacedSE Λ lbl s c0 [])
include hpl0

/-- `c0` with any hold is placed. -/
theorem pl_hold (hd : Option (Nat × TermRun.Word)) (s : State) : PlacedSE Λ lbl s { c0 with hold := hd } [] :=
  Spike.Lib.X64.WakePh.WcWf.PlacedSE.hold.2 (hpl0 s)

/-- **`wc_main` up to the allocator's return inside the placement**, at an
entry invariant whose controls are `c0` (`hJ0`). -/
theorem wcPreW_pl {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (hJ0 : ∀ σ c, J0 σ c → c = c0) :
    WcPreW (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F ms J0 J0 := by
  have h0 : ∀ σ c, J0 σ c → ∀ s, PlacedSE Λ lbl s c [] := fun σ c h s => hJ0 σ c h ▸ hpl0 s
  refine ⟨⟨blkW_q h0, blkW_q fun _ c ⟨σ, hJ, _⟩ => h0 σ c hJ, nodeW_q fun _ c ⟨σ, hJ, _⟩ => h0 σ c hJ,
      blkW_q fun _ c ⟨σ, _, hJ, _⟩ => h0 σ c hJ, blkW_q fun _ c ⟨σ, _, hJ, _⟩ => h0 σ c hJ⟩,
    blkW_q fun _ c ⟨⟨σe, hJe, _⟩, _⟩ => h0 σe c hJe, fun q _ _ => ?_⟩
  refine Spike.Lib.X64SetupPlaced.allocW_of_ctl fun m0 hF s c _ hc => ?_
  obtain ⟨-, -, mC, σC, c', -, ⟨⟨σe, hJe, -⟩, -⟩, hN, -⟩ := hF
  have hq0 : c' = q.c0 := hN.1
  have e0 : q.c0 = c0 := hq0 ▸ hJ0 σe c' hJe
  rcases hc with rfl | ⟨o, rfl⟩
  · rw [e0]; exact hpl0 s
  · show PlacedSE Λ lbl s { q.c0 with hold := _ } []
    rw [e0]; exact pl_hold hpl0 _ s

/-- **`.x18` inside the placement**, at an entry invariant whose controls
are `c0` (`hJ0`): its controls are `c0` with the counter's hold. -/
theorem wcSp0W_pl {ms : Spike.Lib.MemSide isa} {J0 : Spike.Lib.X64.AS → Ctl → Prop}
    (hJ0 : ∀ σ c, J0 σ c → c = c0) :
    WcSp0W (fun s c => PlacedSE Λ lbl s c []) (fun _ _ => False) exe endPc R F ms J0 :=
  ⟨blkW_q fun _ c ⟨q, ⟨σe, hJe, _⟩, _, o, hc, _⟩ s => by
      rw [hc]; show PlacedSE Λ lbl s { q.1.c0 with hold := _ } []
      rw [hJ0 σe _ hJe]; exact pl_hold hpl0 _ s,
    nodeW_q fun _ c ⟨q, o, ⟨σe, hJe, _⟩, hc, _⟩ s => by
      rw [hc]; show PlacedSE Λ lbl s { q.1.c0 with hold := _ } []
      rw [hJ0 σe _ hJe]; exact pl_hold hpl0 _ s⟩

end Pl

/-! ## At `wc_main`'s entry invariant -/

variable {L : RuntimeLayout} {k0 : BitVec 64} {lbl : Lbl} {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa}

/-- **`wc_main` up to the allocator's return inside the placement** at
`MainGlue`'s entry invariant (`WcWfS.wcPreW_WSO`'s `hpl`). -/
theorem hplP_W (hpl0 : ∀ s, PlacedSE L.Λ lbl s c0 []) (σC : Spike.Lib.X64.AS) :
    WcPreW (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) exe endPc R F ms
      (wJ0 (wNC L.lab (JS L k0 c0)).J σC) (wJ0 (wNC L.lab (JS L k0 c0)).J σC) :=
  wcPreW_pl hpl0 fun _ _ h => c0_wJ0 h

/-- **`.x18` inside the placement** at `MainGlue`'s entry invariant
(`WcWfS.wcSp0W_WSO`'s `hpl`). -/
theorem hplS_W (hpl0 : ∀ s, PlacedSE L.Λ lbl s c0 []) (σC : Spike.Lib.X64.AS) :
    WcSp0W (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) exe endPc R F ms
      (wJ0 (wNC L.lab (JS L k0 c0)).J σC) :=
  wcSp0W_pl hpl0 fun _ _ h => c0_wJ0 h

end Spike.Lib.X64.WakePh.WcPl

/-- info: 'Spike.Lib.X64.WakePh.WcPl.hplP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcPl.hplP_W

/-- info: 'Spike.Lib.X64.WakePh.WcPl.hplS_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcPl.hplS_W

/-- info: 'Spike.Lib.X64.WakePh.WcPl.tp_wJ0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcPl.tp_wJ0
