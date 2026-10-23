/-
**The consumer's obligations from one segment inside `W`**: a `SegW W
(TakeK a rS)` from the start fragment to `False` (the program never leaves
it), with every state of `W` carrying the per-state facts of `Nodes`,
`TakePath` and an empty `AbortPath` (`SFacts`), gives the fragment `I` of
`correctA64` with `Nodes`, `TakePath` and `AbortPath` (`Ab` false).

- `SFacts`: the per-state facts, `Nodes`' fields but `out`, `TakePath`'s
  static half at the take site, its phase kept by instructions and system
  calls, `rS` owned in the phase, at an abort site only the overflow one
  with the control about to overflow (`abortOk`), and at a `write` only the
  write tail `Dt` (`wrTail`; with the default `Dt` false, no `write`).
- `abortOk_of_ne`: `abortOk` off every abort site.
- `IOf`: the fragment at the labels' placement `L0` and sizes `ls0`.
- `NoWrite`, `writeNoProm_of_noWrite`: no fragment state at a `write`, which
  discharges the consumer's `WriteNoProm`; `WrIn`: every fragment state at a
  `write` in `Dt` (`NoWrite` at `Dt` false, `TailNoFul.entry` otherwise).
- `inst_of_segW`: the obligations. `Nodes.out` is the segment's `Out`
  closure off the take site (no take moves a state there); `TakePath.site`'s
  pairing after the take is its closure under the take (`KOut`); the
  overflow case of `AbortPath.at_` from `SFacts.abortOk`; `WrIn` from
  `SFacts.wrTail`.
-/
import Spike.Lib.A64Consumer
import Spike.Lib.A64Ret0

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1
open Spike.Lib.A64.Flow.Ret0 (TakeK TakeK.pc)

/-- **The per-state facts** of a thread state `s` paired with `c`, at the
labels' placement `lbl` and sizes `lsize`: `Nodes`' fields but `out`, at the
take site `TakePath.site`'s static half and the take landing in the phase, the phase `Tk` kept by every
instruction off the transfer sites and every system call, `rS` owned in the phase, at an abort site
only the overflow one, the control about to overflow in a small environment with the abort status at
an `exit_group` (`abortOk`: `AbortPath` with an empty phase and its overflow case), and at a `write`
system call only states of the write tail `Dt` (`wrTail`).

`Dt` defaults to false, where `wrTail` says no `write` (`NoWrite`). **Whenever the write tail is live
(a segment through an abort stub's `write`), `Dt` must be given explicitly**: an unannotated
`SFacts … s c` elaborates at the default and silently asks for no `write`. -/
structure SFacts (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (rS : Range) (Tk : State → Prop) (lbl : Lbl)
    (s : State) (c : Ctl) (Dt : State → Prop := fun _ => False) : Prop where
  noRet : ∀ a, c.term ≠ .ret a
  cell : ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : Placed Λ lbl s c
  svc : abi.atSys s = true → ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  noAlloc : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e
  ownInstr : abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree → OwnTree own (own s) tree
  ownSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s
  ownTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, own (abi.skip (abi.setDmem s m)) = own s
  site : ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false ∧
      Kernel.siteRange abi s = rS ∧ rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool
  tkTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, Tk (abi.skip (abi.setDmem s m))
  tkInstr : Kernel.siteAt abi μ s = none → abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  tkSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : Tk s → Owned Λ rS s
  abortOk : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
    ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s

/-- **`SFacts.abortOk` off every abort site.** -/
theorem abortOk_of_ne {μ : Marks} {s : State} {c : Ctl} (h : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .overflow ∧ OvfReady c ∧ EnvSmall c.env ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  fun k a ha hpc => (h k a ha hpc).elim

/-- **The fragment at one placement**: the labels' placement `L0` and
sizes `ls0`, and the pair in `inv`. -/
def IOf (L0 : Lbl) (ls0 : Lsize) (inv : Frag isaLSE2) : Inv := fun lbl lsize s c => lbl = L0 ∧ lsize = ls0 ∧ inv s c

/-- **No fragment state is at a `write`**: at a system call the decoded
call is not a `write`. -/
def NoWrite (I : Inv) : Prop :=
  ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = true → ∀ fd buf n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n)

/-- **Every fragment state at a `write` is in `Dt`**: at a system call
whose decoded call is a `write`. At `Dt` false this is `NoWrite`; otherwise
it is `TailNoFul.entry`'s premise (`Spike/Lib/A64TailNoFul.lean`). -/
def WrIn (I : Inv) (Dt : State → Prop) : Prop :=
  ∀ lbl lsize s c, I lbl lsize s c → abi.atSys s = true → ∀ fd buf n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s

/-- **A number other than `write`'s decodes to no `write`**, whatever the
arguments. -/
theorem decode_ne_write {N : Kernel.Nrs} {nr : Nat} (a : Fin 6 → Nat) (h : nr ≠ N.write) (fd buf n : Nat) :
    Kernel.decode N nr a ≠ some (.write fd buf n) := by
  unfold Kernel.decode
  simp only [h, ite_false]
  repeat' split
  all_goals simp

/-- **`WriteNoProm` from `NoWrite`**: in `Pre` thread 0's state is in the
fragment, so it is not at a `write` and the premise is vacuous. -/
theorem writeNoProm_of_noWrite {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : Own} {I : Inv} {rS : Range} {Tk : State → Prop} {μ : Marks} (h : NoWrite I) :
    WriteNoProm Λ P p G own I rS Tk μ := by
  rintro t s th ⟨th', _, _, lbl, lsize, _, _, _, _, hth, -, -, -, -, -, -, -, -, -, hI, -⟩ hth1 hat ⟨fd, buf, n, hc⟩
  rw [hth] at hth1
  cases Option.some.inj (show some th' = some th from congrArg (·[0]?) hth1)
  exact absurd hc (h lbl lsize _ _ hI hat fd buf n)

/-- A state's pc is the address `a` exactly when its pc register is `a`. -/
theorem pcOf_eq_iff {s : State} {a : Int64} : pcOf s = a.toBitVec.toNat ↔ s.st.2 = a := by
  constructor
  · intro h
    exact Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h)
  · intro h
    rw [pcOf, h]

/-- **The consumer's obligations from one segment inside `W`**, the take
of `rS` at `a` its outside move: the segment's hidden invariant at the
placement `L0`, `ls0` is the fragment, with `Nodes`, `TakePath` and
`AbortPath` with an empty phase, given every state of `W` carries `SFacts`
(`hW`, whose `tkTake` lands every take in the phase) and the take site is
`a` (`hμ`); every fragment state at a `write` is in `Dt` (`WrIn`; at the
default `Dt` false it is `NoWrite`, for `writeNoProm_of_noWrite`). A state
at an abort site is the overflow case of `AbortPath.at_` (`SFacts.abortOk`). -/
theorem inst_of_segW {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Own} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64} {p : Prog} {W P : Frag isaLSE2}
    (h : SegW W (TakeK a rS) p L0 (msOf Λ μ rd G own L0 ls0) P (fun _ _ => False))
    (hμ : μ.site .take = some a.toBitVec.toNat)
    {Dt : State → Prop} (hW : ∀ s c, W s c → SFacts Λ μ own rS Tk L0 s c Dt) :
    ∃ inv : Frag isaLSE2, (∀ s c, P s c → inv s c) ∧ Nodes Λ p μ rd G own (IOf L0 ls0 inv) ∧
      TakePath Λ p μ (IOf L0 ls0 inv) rS Tk ∧ AbortPath μ (IOf L0 ls0 inv) (fun _ => False) ∧
      WrIn (IOf L0 ls0 inv) Dt := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  have hF : ∀ lbl lsize s c, IOf L0 ls0 inv lbl lsize s c → SFacts Λ μ own rS Tk lbl s c Dt := by
    rintro lbl lsize s c ⟨rfl, rfl, hi⟩
    exact hW s c (hiW s c hi)
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  refine ⟨inv, hP, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun lbl lsize s c hi => (hF lbl lsize s c hi).wrTail⟩
  -- `Nodes`
  · rintro lbl lsize s c ⟨rfl, rfl, hi⟩ hoff
    have hk : ∀ s', ¬ TakeK a rS s s' := fun s' hk =>
      hoff _ hμ (pcOf_eq_iff.mpr (TakeK.pc hk))
    exact ((hcl s c hi).1 hk).mono fun s c h => h.elim (fun h => ⟨rfl, rfl, h⟩) False.elim
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).noRet
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).cell
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).noSite
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).mapped
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).place
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).svc
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).noAlloc
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).ownInstr
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).ownSys
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).ownTake
  -- `TakePath`
  · rintro lbl lsize s c hi a' ha' hpc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (hF lbl lsize s c hi).site a' ha' hpc
    refine ⟨h1, h2, h3, h4, h5, h6, h7, fun pm => ?_⟩
    obtain ⟨rfl, rfl, hi⟩ := hi
    have hk : TakeK a rS s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    obtain ⟨c', hr, hi'⟩ := (hcl s c hi).2 _ hk
    exact ⟨c', hr, ⟨rfl, rfl, hi'.elim id False.elim⟩, (hW s c (hiW s c hi)).tkTake a' ha' hpc _⟩
  · exact fun lbl lsize s c hi hn => (hF lbl lsize s c hi).tkInstr hn
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).tkSys
  · exact fun lbl lsize s c hi => (hF lbl lsize s c hi).owned
  -- `AbortPath`, with an empty phase: only the overflow case
  · intro lbl lsize s c hi k a' ha' hpc
    obtain ⟨hk, hc, he, hv⟩ := (hF lbl lsize s c hi).abortOk k a' ha' hpc
    exact ⟨.inr ⟨hk, hc, he⟩, hv⟩
  · exact fun _ _ _ _ _ _ _ tree _ => (allInv_true tree).mono fun _ _ h => h
  · exact fun _ _ _ _ _ _ _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ _ _ _ _ _ h => h

/-! ## `SFacts` at a state without an event -/

/-- **`SFacts`' facts of the source control alone.** -/
structure CFacts (Λ : Scc.Sem.Layout) (lbl : Lbl) (c : Ctl) : Prop where
  noRet : ∀ a, c.term ≠ .ret a
  cell : ∀ x a e ty w,
    (c.term = .let_ x (.load true a) e ∨ ∃ b, c.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c.env a = some (ty, [w]) → OneCellTy ty
  noAlloc : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e
  place : ∀ s, Placed Λ lbl s c

/-- **`SFacts`' facts of the pc off the marks' sites**: no release, take
or abort site. -/
structure PcOff (μ : Marks) (s : State) : Prop where
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  noTake : ∀ a, μ.site .take = some a → pcOf s ≠ a
  noAbort : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a

/-- No take at a state off the take site. -/
theorem PcOff.not_take {μ : Marks} {s : State} {a : Int64} {rS : Range} (h : PcOff μ s)
    (hμ : μ.site .take = some a.toBitVec.toNat) : ∀ s', ¬ TakeK a rS s s' := fun _ hk =>
  h.noTake _ hμ (pcOf_eq_iff.mpr (TakeK.pc hk))

/-- **`SFacts` at an instruction without an event** (not an `svc`, its step
`.done s'`), off the marks' sites: the leaf owns what `s` owns and is in
the phase iff `s` is; in the phase the range is owned. -/
theorem sfacts_done {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
    {s s' : State} {c : Ctl} {d : Directive} {sz : Nat} (hC : CFacts Λ lbl c) (hP : PcOff μ s)
    (hc : Kraken.Promising.Lower.A64.CellAt s d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hex : isaLSE2.exec s = some (.done s')) (hown : own s' = own s) (htk : Tk s' ↔ Tk s)
    (hO : Tk s → Owned Λ rS s) : SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hc hd
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun _ e he => ?_, hC.place s, fun h => ?_, hC.noAlloc,
    fun _ tree he => ?_, fun h => ?_, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ _ tree he => ?_,
    fun h => ?_, hO, abortOk_of_ne hP.noAbort, fun h => ?_⟩
  · rw [hex] at he; cases he; nofun
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact .inl ⟨hown, trivial⟩
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact htk
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

/-! ## `SFacts` at an instruction with events -/

section Ev

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {s : State} {c : Ctl}

open Kraken.Promising.Lower.A64 (CellAt after)

/-- **`SFacts` at an instruction off a system call**, off the marks'
sites: its tree touches no location the loaded kernel state leaves
unmapped, keeps the owned words (`OwnTree`), and every leaf is in the phase
iff `s` is. -/
theorem sfacts_ev {d : Directive} {sz : Nat} {tree : EvTree State} (hC : CFacts Λ lbl c) (hP : PcOff μ s)
    (hc : CellAt s d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec s = some tree)
    (hT : ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) tree) (hown : OwnTree own (own s) tree)
    (htk : tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)) (hO : Tk s → Owned Λ rS s) :
    SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hc hd
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun _ e he => ?_, hC.place s, fun h => ?_, hC.noAlloc,
    fun _ t he => ?_, fun h => ?_, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ _ t he => ?_,
    fun h => ?_, hO, abortOk_of_ne hP.noAbort, fun h => ?_⟩
  · rw [hex] at he; cases he; exact hT
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact hown
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact htk
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

/-- **A plain or release store of `V` to `⟨a, 8⟩`, its leaf past it**:
mapped for writing in the loaded kernel state, the leaf in the phase iff
`s` is; a word `s` does not own is kept (`OwnTree`'s first case), an owned
word is updated (`hupd`, its third). -/
theorem store_facts {k : Kraken.StoreKind} {a : BitVec 64} {V : Val} {m : MachineData}
    (hmp : Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true) (htk : Tk (after s 4 m) ↔ Tk s)
    (hown : (own (after s 4 m) = own s ∧ ∀ w, (⟨a, 8⟩, w) ∉ own s) ∨ OwnUpd (own s) (own (after s 4 m)) ⟨a, 8⟩ V) :
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false)
        (.store k false ⟨a, 8⟩ V fun _ => .done (after s 4 m) : EvTree State) ∧
      OwnTree own (own s) (.store k false ⟨a, 8⟩ V fun _ => .done (after s 4 m)) ∧
      (EvTree.store k false ⟨a, 8⟩ V fun _ => .done (after s 4 m)).AllInv (fun _ _ => True)
        (fun s' => Tk s' ↔ Tk s) := by
  refine ⟨fun h => ?_, ?_, ⟨trivial, fun _ _ => htk⟩⟩
  · cases h with
    | store h => rw [hmp] at h; cases h
    | storeRet _ h => cases h
  · rcases hown with ⟨he, hn⟩ | hu
    · exact .inl ⟨⟨trivial, fun _ _ => he⟩, fun w => hn w, fun _ => trivial⟩
    · exact .inr (.inr (.inl ⟨k, _, _, _, rfl, rfl, hu⟩))

/-- **A plain load of `⟨a, 8⟩`, its leaves past it**: mapped for reading in
the loaded kernel state; every leaf owns what `s` owns and is in the phase
iff `s` is. -/
theorem load_facts {k : Kraken.LoadKind} {a : BitVec 64} {m : Val → MachineData}
    (hmp : Kernel.mapped (K0 Λ) false ⟨a, 8⟩ = true) (htk : ∀ v, Tk (after s 4 (m v)) ↔ Tk s)
    (hown : ∀ v, own (after s 4 (m v)) = own s) :
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false)
        (.load k false ⟨a, 8⟩ fun v => .done (after s 4 (m v)) : EvTree State) ∧
      OwnTree own (own s) (.load k false ⟨a, 8⟩ fun v => .done (after s 4 (m v))) ∧
      (EvTree.load k false ⟨a, 8⟩ fun v => .done (after s 4 (m v))).AllInv (fun _ _ => True)
        (fun s' => Tk s' ↔ Tk s) := by
  refine ⟨fun h => ?_, .inl ⟨fun v _ => hown v, fun _ => trivial⟩, fun v _ => htk v⟩
  cases h with
  | load h => rw [hmp] at h; cases h
  | loadRet _ h => cases h

/-- **An RMW of an owned word `⟨a, 8⟩`, its leaves past it**: mapped for
writing in the loaded kernel state; every leaf owns the word at the value
written (`OwnTree`'s fourth case) and is in the phase iff `s` is. -/
theorem rmw_facts {k : Kraken.RmwKind} {nr : Bool} {a : BitVec 64} {op : Val → Option Val}
    {m : Val → MachineData} (hmp : Kernel.mapped (K0 Λ) true ⟨a, 8⟩ = true)
    (htk : ∀ v, Tk (after s 4 (m v)) ↔ Tk s) (hin : ∃ v, (⟨a, 8⟩, v) ∈ own s)
    (hupd : ∀ v, (⟨a, 8⟩, v) ∈ own s → OwnUpd (own s) (own (after s 4 (m v))) ⟨a, 8⟩ ((op v).getD v)) :
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false)
        (.rmw k nr ⟨a, 8⟩ op fun v => .done (after s 4 (m v)) : EvTree State) ∧
      OwnTree own (own s) (.rmw k nr ⟨a, 8⟩ op fun v => .done (after s 4 (m v))) ∧
      (EvTree.rmw k nr ⟨a, 8⟩ op fun v => .done (after s 4 (m v))).AllInv (fun _ _ => True)
        (fun s' => Tk s' ↔ Tk s) := by
  refine ⟨fun h => ?_, .inr (.inr (.inr ⟨k, nr, _, op, _, rfl, rfl, hin, hupd⟩)),
    fun v _ => ⟨fun _ _ => trivial, htk v⟩⟩
  cases h with
  | rmw h => rw [hmp] at h; cases h
  | rmwRet _ h => cases h

/-- **`SFacts` at a single instruction without an event** (`SI`: `adrp`,
`add :lo12:`, `nop`, `msr`) off the marks' sites. -/
theorem sfacts_si {si : Spike.Lib.A64.Flow.SI} (hC : CFacts Λ lbl c) (hP : PcOff μ s) (hc : CellAt s si.toDir 4)
    (hnext : ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s) :
    SFacts Λ μ own rS Tk lbl s c :=
  sfacts_done hC hP hc (by cases si <;> intro imm h <;> cases h) (Spike.Lib.A64.Flow.exec_si hc)
    (hnext _).1 (hnext _).2 hO

/-- **`SFacts` at `svc #0`** off the marks' sites: every state the kernel
resumes in is past it, owning what `s` owns and in the phase iff `s` is; the
call is not a `write` (`hnw`). -/
theorem sfacts_svc (hC : CFacts Λ lbl c) (hP : PcOff μ s) (hc : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) = own s ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hnw : ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n)) :
    SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = true := atSvc_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
    exact hnext _
  refine ⟨hC.noRet, hC.cell, hP.noSite, fun h => ?_, hC.place s, fun _ => ⟨0, 4, hc⟩, hC.noAlloc,
    fun h => ?_, fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, abortOk_of_ne hP.noAbort, fun _ => hnw⟩
  all_goals (rw [hs] at h; cases h)

/-- **`SFacts` at the take site** (a `nop`, at no release or abort site): before the phase, `x0`/`x1`
naming `rS` in the pool (`hsite`), the take landing in the phase (`htake`); the take's leaf and the
`nop`'s own what `s` owns. The `nop` as an instruction need not keep the phase: `tkInstr` asks it off
the transfer sites only, and the pc is the take site (`hat`). -/
theorem sfacts_site (hC : CFacts Λ lbl c)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (hab : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a)
    (hc : CellAt s (.instr ⟨.W64, .NOP⟩) 4) (htk : ¬ Tk s)
    (hsite : Kernel.siteRange abi s = rS ∧ rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool)
    (hown : ∀ m, own (after s 4 m) = own s) (htake : ∀ m, Tk (abi.skip (abi.setDmem s m)))
    (hat : μ.site .take = some (pcOf s)) :
    SFacts Λ μ own rS Tk lbl s c := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro imm h; cases h)
  have hex := Kraken.Promising.Lower.A64.exec_nop hc
  refine ⟨hC.noRet, hC.cell, hrel, fun _ e he => ?_, hC.place s, fun h => ?_, hC.noAlloc,
    fun _ t he => ?_, fun h => ?_, fun _ _ _ m => ?_, fun a' ha' _ => ⟨htk, ⟨4, hc⟩, hs, hsite⟩,
    fun _ _ _ m => htake m,
    fun hn => absurd hn (by simp [Kernel.siteAt, abi, hat]), fun h => ?_, fun h => (htk h).elim, abortOk_of_ne hab,
    fun h => ?_⟩
  · rw [hex] at he; cases he; nofun
  · rw [hs] at h; cases h
  · rw [hex] at he; cases he; exact .inl ⟨hown _, trivial⟩
  · rw [hs] at h; cases h
  · have hn : abi.skip (abi.setDmem s m) = after s 4 { s.st.1 with dmem := m } := by
      show { s with st := ({ s.st.1 with dmem := m }, nextPc (abi.setDmem s m)) } = _
      rw [nextPc_of_cellAt (st := abi.setDmem s m) ⟨hc.valid, hc.ne, hc.code⟩]; rfl
    rw [hn]; exact hown _
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

end Ev

/-! ## A covered block's states -/

section Blk

open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)

/-- A covered instruction is not an `svc`. -/
theorem AI.not_svc {a : AI} (hreg : ∀ w op, a = .reg w op → RegOnly op = true) :
    ∀ imm, a.toDir ≠ .instr ⟨.W64, .SVC imm⟩ := by
  intro imm h
  cases a <;> simp only [AI.toDir, Directive.instr.injEq, Instr.mk.injEq, heq_eq_eq, reduceCtorEq, and_false] at h
  rename_i w op
  obtain ⟨rfl, h⟩ := h
  cases h
  exact absurd (hreg _ _ rfl) (by simp [RegOnly])

/-- **A covered block's states carry `SFacts`**, none moved by `K`: the
source control's facts at the node (`hC`), the pcs' off the marks' sites
and no outside move there (`hpc`), each instruction's leaf owning what its
state owns and in the phase iff it is, at the abstract run's next pc
(`hph`), and in the phase the range owned at the block's memories and pcs
(`hO`). -/
theorem blkW_sfacts {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s ∧ ∀ s', ¬ K s s')
    (hph : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s s' : State,
      s.exe = exe → s.endPc = endPc → s'.exe = exe → s'.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      own s' = own s ∧ (Tk s' ↔ Tk s))
    (hO : ∀ (s : State) m, F s.st.1 → DFrame R s.st.1 m → (∀ k, R.Off k → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ k < blk.length, ∀ s' : State, s'.st.1 = m → s'.st.2 = n.pc + Int64.ofNat (4 * k) → Tk s' → Owned Λ rS s') :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  intro s σ c he hn _ hpc0 hA hF hJ k hk m hA' hD
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hl : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA'
  rw [hl] at hex
  obtain ⟨hown, htk⟩ := hph σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } he hn he hn rfl rfl
  exact sfacts_done (hC σ c hJ) hP hc (AI.not_svc hreg) hex hown htk
    (hO s m hF hD (fun k' hk' => Option.isSome_iff_exists.mpr (by
      obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)) k hk _ rfl rfl)

/-! ### Phases by pc

When the owned words and the phase are functions of a phase index `ph` of
the pc, a block's `hpc` and `hph` are one Boolean check on the program
(`blkPh`): every pc of the block is off the sites (`okPc`) and in the
block's phase, and so is every target of every instruction but a dead one
(`dead`: a target the node's invariant rules out, `hdead`). A `ret`'s
target is the return address `ra` the node's invariant gives (`hret`). -/

/-- **The targets of a covered instruction**: the next pc `fall`, a
branch's label, both for a conditional branch, the return address `ra` for
a `ret`. -/
def aiTgts (lab : Label → Int64) (fall ra : Int64) : AI → List Int64
  | .b L | .bl L => [lab L]
  | .bcond _ L | .cbz _ L | .cbnz _ L => [lab L, fall]
  | .ret _ => [ra]
  | _ => [fall]

theorem aiTgt_mem {lab : Label → Int64} {fall ra : Int64} {σ : AS} (a : AI)
    (hr : ∀ r, a = .ret r → Int64.ofInt (σ.regs.getRegOrZr r).signed = ra) :
    a.tgt lab fall σ ∈ aiTgts lab fall ra a := by
  cases a <;> simp only [AI.tgt, aiTgts, List.mem_cons, List.not_mem_nil, or_false]
  all_goals first
    | exact hr _ rfl
    | (split <;> simp)
    | simp

/-- **A block's phase check**: every pc of the block is off the sites
(`okPc`) and has the entry's phase, and so has every target of every
instruction (a `ret`'s the return address `ra`) but a dead one (`dead`). -/
def blkPh (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Nat → Bool) (lab : Label → Int64) (pc ra : Int64)
    (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat &&
    ph (pc + Int64.ofNat (4 * k)).toBitVec.toNat == ph pc.toBitVec.toNat &&
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          ph t.toBitVec.toNat == ph pc.toBitVec.toNat || dead t.toBitVec.toNat
      | none => false
    | none => false

/-- **`blkW_sfacts`' `hpc` and `hph` from the check** on a covered block,
and every pc of the block in the entry's phase:
the owned words and the phase factor through `ph` of the pc (`hsame`),
off-site pcs carry `PcOff` and no outside move (`hok`), every `ret` of the
block returns to `ra` (`hret`) and the block's run never ends at a dead pc
(`hdead`). -/
theorem blkPh_sound {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
    {exe : _root_.Executable} {endPc : Int64} {n : ND} {blk : List Directive} {okPc : Nat → Bool}
    {ph : Nat → Nat} {dead : Nat → Bool} {ra : Int64} {lo hi : Int}
    (hsame : ∀ s s' : State, ph (pcOf s') = ph (pcOf s) → own s' = own s ∧ (Tk s' ↔ Tk s))
    (hok : ∀ s : State, okPc (pcOf s) = true → PcOff μ s ∧ ∀ s', ¬ K s s')
    (hb : okBlk lo hi n.o blk = true)
    (h : blkPh okPc ph dead (_root_.Executable.labels exe).label n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra)
    (hdead : ∀ σ c, n.J σ c →
      dead (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false) :
    (∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s ∧ ∀ s', ¬ K s s') ∧
    (∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s s' : State,
      s.exe = exe → s.endPc = endPc → s'.exe = exe → s'.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      own s' = own s ∧ (Tk s' ↔ Tk s)) ∧
    (∀ k < blk.length, ∀ s s' : State, s.st.2 = n.pc → s'.st.2 = n.pc + Int64.ofNat (4 * k) →
      own s' = own s ∧ (Tk s' ↔ Tk s)) := by
  have hk : ∀ k (hk : k < blk.length), okPc (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat = true ∧
      ph (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat = ph n.pc.toBitVec.toNat ∧
      ∀ a, classify blk[k] = some a → ∀ t ∈ aiTgts (_root_.Executable.labels exe).label
        (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a,
        ph t.toBitVec.toNat = ph n.pc.toBitVec.toNat ∨ dead t.toBitVec.toNat = true := by
    intro k hk
    have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    rw [List.getElem?_eq_getElem hk] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, h2, fun a ha t ht => ?_⟩
    rw [ha] at h3
    simpa only [Bool.or_eq_true, beq_iff_eq] using List.all_eq_true.mp h3 t ht
  refine ⟨fun k hkl s _ _ hpc => hok s (by unfold pcOf; rw [hpc]; exact (hk k hkl).1), ?_,
    fun k hkl s s' hpc hpc' => hsame s s' (by unfold pcOf; rw [hpc, hpc', (hk k hkl).2.1])⟩
  intro σ c hJ k hkl a ha s s' _ _ _ _ hpc hpc'
  refine hsame s s' ?_
  unfold pcOf
  rw [hpc, hpc', (hk k hkl).2.1]
  rcases (hk k hkl).2.2 a ha _ (aiTgt_mem a fun r hr => hret σ c hJ k hkl r (hr ▸ ha)) with h' | hd
  · exact h'
  -- a dead target: the instruction is the last, its target the block run's end
  obtain ⟨a', ha', -, hterm⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hb hkl
  rw [ha] at ha'
  cases ha'
  by_cases hl : k + 1 < blk.length
  · rw [AI.tgt_of_not_term (hterm hl), Spike.Lib.A64.Flow.Ret0.ofNat4_succ']
    exact (hk (k + 1) hl).2.1
  · have he : k + 1 = blk.length := by omega
    have hrun := arun_take_succ (_root_.Executable.labels exe).label hkl ⟨n.pc, n.o, σ⟩
    rw [he, List.take_length] at hrun
    have hpk := arun_pc (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hb hkl
    have hd' := hdead σ c hJ
    rw [hrun] at hd'
    simp only [dstep, ha, hpk] at hd'
    rw [hd'] at hd
    cases hd

/-- **`blkPh_sound`'s `hret` from the block's run**: a `ret` of a covered
block is its last instruction, so it returns to where the block's run ends
(`h`, a walk lemma's pc). -/
theorem hret_of_run {lab : Label → Int64} {lo hi : Int} {n : ND} {blk : List Directive} {ra : Int64}
    (hb : okBlk lo hi n.o blk = true) (h : ∀ σ c, n.J σ c → (arun lab blk ⟨n.pc, n.o, σ⟩).pc = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra := by
  intro σ c hJ k hk r hr
  obtain ⟨a, ha, -, hterm⟩ := okBlk_get lab (am := ⟨n.pc, n.o, σ⟩) hb hk
  rw [hr] at ha
  cases ha
  have hl : ¬ k + 1 < blk.length := fun hl => by have := hterm hl; cases this
  have hrun := arun_take_succ lab hk ⟨n.pc, n.o, σ⟩
  rw [show k + 1 = blk.length by omega, List.take_length] at hrun
  have := h σ c hJ
  rw [hrun] at this
  simpa only [dstep, hr, AI.tgt] using this

/-- **A block without `ret`.** -/
def noRetBlk (blk : List Directive) : Bool :=
  blk.all fun d => match classify d with
    | some (.ret _) => false
    | _ => true

/-- A block without `ret` has no `ret` at any index (`blkPh_sound`'s
`hret` for any return address). -/
theorem noRet_false {blk : List Directive} (h : noRetBlk blk = true) :
    ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) → False := by
  intro k hk r hr
  have := List.all_eq_true.mp h _ (List.getElem_mem hk)
  rw [hr] at this
  cases this

end Blk

end Spike.Lib.A64Consumer
