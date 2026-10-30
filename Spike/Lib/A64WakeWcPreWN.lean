/-
**`wc_main`'s nodes before `.sp4` inside `SFactsSt2` at `ownG`** (AArch64): the second part of `A64WakeWcPreW`. These are single-instruction
nodes: the prologue's limit load, the box store at `.sp0`, and the fence
after it. Each node lemma is proved at the first instance (`instOkW`) at
the entry control `c0`. It is then moved to `ownG`, which picks `ownW` at
the node's pc and at the next one (both free, `freeN`).

- `nodeW_dmb_pre`: a fence `dmb` node inside `SFacts`, for any program
  (no `SFacts` lemma for `DMB` existed).
- `succ_pc4`: a successor of a 4-byte non-`svc` cell whose leaves are 4
  bytes on, off the take site, is 4 bytes on.
- `nodeAgreeW`: `ownG` agrees with `ownW` at a node whose pc and next pc
  are free.
- `c0N`, `nodeW_wcG`: a node's obligation at `ownG` from the instance's,
  proved at the entry control `c0`.
- `NodeW.ofAll`: a node's obligation, split over a function of the state.
-/
import Spike.Lib.A64WakeWcPreW

namespace Spike.Lib.A64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhFact okPcOf codeT codeT_eq factOk blockAt pcAt)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem (Marks Range TreeLeaf)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64Consumer (Lbl CFacts SFacts)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Kraken.Promising.Lower.A64 (CellAt after)

/-! ## A fence node inside `SFacts` -/

section Dmb

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64Consumer.Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node at a fence `dmb`** before the take, its next pc in its phase:
the fence touches no location and keeps the owned words. -/
theorem nodeW_dmb_pre {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {fk : FenceKind} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [.instr ⟨.W64, .DMB fk⟩] = true) (he : lab l + Int64.ofNat (4 * k) = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc p.toBitVec.toNat = true)
    (hT : ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  Spike.Lib.A64.Rt.nodeW_pre hI hp hok hT fun s c σ hs hn _ hpc _ _ hJ hP hO => by
    have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
    have hsm := Spike.Lib.A64.Rt.next_same hI hpc hph s.st.1
    refine Spike.Lib.A64Consumer.sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h)
      (Kraken.Promising.Lower.A64.exec_dmb hc) ?_ (.inl ⟨fun _ => hsm.1, fun _ => trivial⟩) (fun _ => hsm.2) hO
    intro h
    cases h with
    | fence h => cases h

end Dmb

/-! ## A successor's pc -/

/-- **A successor of a 4-byte cell off `svc`** whose tree's leaves are 4
bytes on (`hl`), off the take site (`hns`), is 4 bytes on. -/
theorem succ_pc4 {μ : Marks} {s s' : State} {d : Directive} {tree : EvTree State} (hc : CellAt s d 4)
    (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec s = some tree)
    (hl : ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4)
    (hns : ∀ a, μ.site .take = some a → pcOf s ≠ a) (h : StSucc μ s s') : s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  have hs : abi.atSys s = false := Scc.Sem.A64.atSvc_false_of_cellAt hc hd
  rcases h with ⟨-, tree', htr, hl'⟩ | ⟨hs', -⟩ | ⟨a, ha, hpc, -⟩
  · rw [hex] at htr; cases htr; exact hl s' hl'
  · rw [hs] at hs'; cases hs'
  · exact absurd hpc (hns a ha)

/-! ## A node's agreement -/

section Agree

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Marks} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND}

/-- **`ownG` agrees with `ownW` at a node** whose pc and next pc are free
(`hf0`, `hf4`), each of its states at a 4-byte cell off `svc` whose leaves
are 4 bytes on (`hstep`). -/
theorem nodeAgreeW (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : μ.site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hf0 : freeN n.pc.toBitVec.toNat = true) (hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧ (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧
      isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s'))) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  have hpc : s.st.2 = n.pc := hAt.2.2.2.1
  have hp0 : pcOf s = n.pc.toBitVec.toNat := by unfold pcOf; rw [hpc]
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hAt
  refine ⟨⟨ownG_W hlab (goodW_of_freeN hlab (by rw [hp0]; exact hf0)), fun s' h => ?_⟩, fun _ h => h⟩
  have hns : ∀ x, μ.site .take = some x → pcOf s ≠ x := by
    intro x hx; rw [hsite] at hx; cases hx; rw [hp0]; exact site_ne_of_freeN hlab hf0
  have e := succ_pc4 hc hd hex hl hns h
  refine ownG_W hlab (goodW_of_freeN hlab ?_)
  unfold pcOf; rw [e, hpc]; exact hf4

end Agree

/-! ## A node at `ownG` from the instance's -/

/-- **A node at the entry control `c0`**: same pc and offsets, the
control `c0` with one of `n`'s at the same state. -/
def c0N (n : ND) : ND := ⟨n.pc, n.o, fun σ c => c = Spike.Lib.A64Consumer.c0 ∧ ∃ c', n.J σ c'⟩

/-- `c0N`'s controls have the consumer's facts. -/
theorem c0N_cfacts {Λ : Scc.Sem.Layout} {lbl : Lbl} {n : ND} :
    ∀ σ c, (c0N n).J σ c → CFacts Λ lbl c :=
  fun _ _ hJ => hJ.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0

section Move

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {rS : Range} {TkW : Nat → Prop}
  {lbl : Lbl} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A node of `wc_main` inside `SFactsSt2` at `ownG`** from the
instance's `SFacts` at `c0N n` (`h`), its pc and next pc free (`hf0`,
`hf4`), each state at a 4-byte cell off `svc` whose leaves are 4 bytes on
(`hstep`). -/
theorem nodeW_wcG (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) {K : State → State → Prop} {n : ND}
    (h : NodeW (fun s c => SFacts Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
      (fun s => TkW (phW (pcOf s))) lbl s c) K L.exe L.endPc R F (c0N n))
    (hf0 : freeN n.pc.toBitVec.toNat = true) (hf4 : freeN (n.pc + Int64.ofNat 4).toBitVec.toNat = true)
    (hstep : ∀ s c, At L.exe L.endPc R F n s c → ∃ d tree, CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s) K L.exe L.endPc R F n := by
  have hag := nodeAgreeW (a := a) (n := c0N n) (exe := L.exe) (endPc := L.endPc) (R := R) (F := F) hlab hsite
    hf0 hf4 fun s c ⟨h1, h2, h3, h4, σ, hA, hF, _, c', hJ⟩ => hstep s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  have h2 := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 h) hag
  exact nodeW_mapC (n' := c0N n) rfl rfl h2 fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

end Move

/-! ## A node split over a function of the state -/

/-- **A node's obligation from its restrictions** to each value `x` of a
function `f` of the abstract state. -/
theorem NodeW.ofAll {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {β : Type} (f : Spike.Lib.A64.Flow.AS → β)
    (h : ∀ x, NodeW W K exe endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ f σ = x⟩) : NodeW W K exe endPc R F n :=
  fun s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ => h (f σ) s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ, rfl⟩

/-- info: 'Spike.Lib.A64.WakePh.WcW.nodeW_dmb_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.nodeW_dmb_pre

/-- info: 'Spike.Lib.A64.WakePh.WcW.nodeW_wcG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcW.nodeW_wcG

end Spike.Lib.A64.WakePh.WcW
