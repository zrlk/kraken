/-
**`SFactsS` at the empty frames from `SFacts`** for an `Accepted1` program
(x86-64): the per-pair facts of a segment at depth 0 (the runtime's own
states, lifted by `SegWS.liftS`) at a pair whose control with no frame is
`Good1` (`Spike/Lib/Frames1.lean`).

- `SFactsS.ofSFacts`: the fields quantified over the frame runs from the
  pair (`cell`, `noAlloc`) from `good1_run` (no load, store or buffer
  allocation is reached); the owned words' fields at the frames reached
  (`ownRun`, `ownInstr`, `ownSys`) are premises; the rest are `SFacts`' at
  `own · []`.
- `SFactsS.ofSFacts0`: for owned words not depending on the frames, all
  from `SFacts`.
- `SFactsS.ofSFactsAt`: at a `Good1` pair `(c, fs)` (a callee's state on
  the deep abort path), from `SFacts` at `c`, the suspended frames placed
  (`FramesPlaced`) and their environments small, for owned words not
  depending on the frames.
- `msAgree_msOfS`: for such owned words, the memory sides at the frames
  agree with depth 0's (`SegWS.lag`'s `hms`).
-/
import Spike.Lib.X64SegInstS
import Spike.Lib.X64PlacedS
import Spike.Lib.Frames1
import Spike.Lib.SegLagS

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
  {cells ctr : Nat} {s : State} {c : Ctl} {Dt : State → Prop}

/-- **`SFactsS` at the empty frames from `SFacts`** at the owned words with
no frame, at a `Good1` pair of an `Accepted1` program, given the owned
words' fields at the frames its runs reach. -/
theorem SFactsS.ofSFacts {own : OwnS} (h : SFacts Λ μ (fun s => own s []) rS Tk lbl s c Dt)
    (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, []))
    (hownRun : ∀ c₁ fs₁ c₂ fs₂, FrameRun p (c₁, fs₁) (c₂, fs₂) → ((c₁ = c ∧ fs₁ = []) ∨ (c₂ = c ∧ fs₂ = [])) →
      own s fs₂ = own s fs₁)
    (hownInstr : ∀ c' fs', FrameRun p (c, []) (c', fs') → abi.atSys s = false → ∀ tree,
      isa.exec s = some tree → OwnTree (own · fs') (own s fs') tree)
    (hownSys : ∀ c' fs', FrameRun p (c, []) (c', fs') → abi.atSys s = true → ∀ call,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
        own s' fs' = own s fs') :
    SFactsS Λ μ p own rS Tk lbl cells ctr s c [] Dt where
  noRet := fun _ => h.noRet
  cell := fun c' fs' hr x a e ty w hc => by
    have hg' := good1_run hp hr hg
    rcases hc with hc | ⟨b, hc⟩
    · exact (hg'.not_load x true a e hc).elim
    · exact (hg'.not_store x true a b none e hc).elim
  noSite := h.noSite
  mapped := h.mapped
  place := PlacedS.ofNil h.place
  svc := h.svc
  noAlloc := fun c' fs' hr => (good1_run hp hr hg).not_newBuf
  ownRun := hownRun
  ownInstr := hownInstr
  ownSys := hownSys
  ownTake := h.ownTake
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  abortOk := fun k a ha hpc => by
    obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
    exact ⟨.inl ⟨hk, ho, he, fun _ hf => by simp at hf⟩, hx⟩
  wrTail := h.wrTail

/-- **`SFactsS` at the empty frames from `SFacts`** for owned words not
depending on the frames. -/
theorem SFactsS.ofSFacts0 {own : Own} (h : SFacts Λ μ own rS Tk lbl s c Dt)
    (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, [])) :
    SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cells ctr s c [] Dt :=
  SFactsS.ofSFacts h hp hg (fun _ _ _ _ _ _ => rfl) (fun _ _ _ => h.ownInstr) (fun _ _ _ => h.ownSys)

/-- **`SFactsS` at the frames `fs` from `SFacts`** for owned words not
depending on the frames, at a `Good1` pair of an `Accepted1` program: the
current control's facts, the suspended frames placed (`hfp`) and their
environments small (`hes`, `EnvSmallS` with the current one's from
`SFacts.abortOk`). -/
theorem SFactsS.ofSFactsAt {own : Own} {fs : List TermRun.Frame} (h : SFacts Λ μ own rS Tk lbl s c Dt)
    (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, fs)) (hfp : FramesPlaced Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) :
    SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cells ctr s c fs Dt where
  noRet := fun _ => h.noRet
  cell := fun c' fs' hr x a e ty w hc => by
    have hg' := good1_run hp hr hg
    rcases hc with hc | ⟨b, hc⟩
    · exact (hg'.not_load x true a e hc).elim
    · exact (hg'.not_store x true a b none e hc).elim
  noSite := h.noSite
  mapped := h.mapped
  place := PlacedS.ofFrames h.place hfp
  svc := h.svc
  noAlloc := fun c' fs' hr => (good1_run hp hr hg).not_newBuf
  ownRun := fun _ _ _ _ _ _ => rfl
  ownInstr := fun _ _ _ => h.ownInstr
  ownSys := fun _ _ _ => h.ownSys
  ownTake := h.ownTake
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  abortOk := fun k a ha hpc => by
    obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
    exact ⟨.inl ⟨hk, ho, he, hes⟩, hx⟩
  wrTail := h.wrTail

/-- **The memory sides at the frames agree** (`SegWS.lag`'s `hms`) when the
owned words do not depend on the frames: `msOfS` differs only in the
placement of `main`'s exit. -/
theorem msAgree_msOfS {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {lsize : Lsize} :
    MsAgree (msOfS Λ μ rd G (fun s _ => own s) lbl lsize) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end Spike.Lib.X64ConsumerS
