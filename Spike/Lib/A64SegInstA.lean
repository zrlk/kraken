/-
**The allocation-capable consumer's obligations from two segment levels**
(the allocation twin of `Spike/Lib/A64SegInstS.lean`): a program that
allocates once has a fragment at the labels' placement `L0` before the
allocation and, for every fresh label `l` the arena places at `b` with `n`
bytes, a fragment at the extended placement after it. Each level is a
segment with its invariant explicit (`SegInvS`); the post-allocation ones
allocate no further (their memory side's allocation fragment false), the
pre-allocation one's allocation lands in them. With every pair of either
level carrying `SFactsA`, the union `I2` is the fragment `I` of `correctKA`
(`Spike/Lib/A64ConsumerACorrect.lean`) with `NodesA`, `TakePathS` and
`AbortPathS` at any abort phase `Ab`.

- `upd`, `updN`: the placement and sizes with `l` placed at `b` with `n`
  bytes (as `msOfA`'s `xa` writes them).
- `SegInvS`: `SegWS` with its invariant the witness and no exit;
  `SegInvS.ofSegWS`: from a `SegWS` to `False`.
- `I2`: the fragment of one allocation.
- `Out.mono_xa`, `OutS.mono_xa`: a row is one under a memory side with a
  larger allocation fragment (the alloc row is the only one reading `xa`).
- `SFactsA`: `SFactsS` without `noAlloc`, with the arena's write obligation
  (`wr`, `WrOkA`, `Spike/Lib/A64ConsumerAWr.lean`), the buffer types' zero
  check (`zero`, `ZeroOkTy`, `Spike/Lib/ZeroTy.lean`) and the abort phase
  `Ab` (`abortOk`, `abInstr`, `abSys`, `abTake`: `AbortPathS`'s fields at
  the pair; the heap case `HeapAbortObl`, `Spike/Lib/HeapObl.lean`).
  `abInstr_false`, `abSys_false`, `abTake_false`, `abortOk_false`: the phase
  fields with `Ab` false.
- `writeNoPromA_of_wrIn`: `WriteNoPromA` from `WrInS` and a closed tail.
- `inst_of_segWA2`: the obligations. `NodesA.out` is either level's `OutS`
  closure off the take site (the post-allocation level's lifted by
  `OutS.mono_xa`); `ctrRow` and `arena` from `SFactsA.wr` and an `Out` row
  at the state (the segment's, or `nop`'s at the take site); `zero` from
  `zero_of_zeroOkTy`; the rest as in `inst_of_segWS`.
-/
import Spike.Lib.A64SegInstS
import Spike.Lib.A64ConsumerAWr
import Spike.Lib.A64ConsumerACorrect
import Spike.Lib.CertClosed
import Spike.Lib.ZeroTy
import Spike.Lib.HeapObl

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow.Ret0 (TakeK TakeK.pc)
open Spike.Lib.HeapLand (AllocLand)

variable {p : Prog}

/-! ## Placements, segments, the fragment -/

/-- The placement with `l` placed at `b` (as `msOfA`'s `xa` writes it). -/
def upd (L : Lbl) (l : WeakMem.AllocLabel) (b : Nat) : Lbl := fun l' => if l' = l then some b else L l'

/-- The sizes with `l` of `n` bytes (as `msOfA`'s `xa` writes them). -/
def updN (ls : Lsize) (l : WeakMem.AllocLabel) (n : Nat) : Lsize := fun l' => if l' = l then n else ls l'

/-- **A segment with its invariant explicit**: `SegWS` with `P := inv`, the
witness `inv`, no exit. -/
def SegInvS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isaLSE2) (inv : FragS isaLSE2) : Prop :=
  ∀ s c fs, inv s c fs →
    W s c fs ∧ ((∀ s', ¬ K s s') → OutS p lbl ms (Pend p inv) s c fs) ∧ KOutS K p inv s c fs

/-- **The witness of a segment with no exit.** -/
theorem SegInvS.ofSegWS {W P : FragS isaLSE2} {K : State → State → Prop} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} (h : SegWS W K p lbl ms P (fun _ _ _ => False)) :
    ∃ inv, (∀ s c fs, P s c fs → inv s c fs) ∧ SegInvS W K p lbl ms inv := by
  obtain ⟨inv, hP, hW, hcl⟩ := h
  refine ⟨inv, hP, fun s c fs hi => ⟨hW s c fs hi, fun hk => ?_, ?_⟩⟩
  · exact ((hcl s c fs hi).1 hk).mono fun _ _ _ h => h.mono fun _ _ _ h => h.elim id False.elim
  · exact (hcl s c fs hi).2.mono fun _ _ _ h => h.elim id False.elim

/-- **The fragment of one allocation**: before it at `L0`, `ls0` (`inv0`);
after it, for a fresh `l` placed at `b` with `n` bytes where the arena can
hand them out (`AllocLand`), at the extended placement (`inv1 l b n`). -/
def I2 (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (inv0 : FragS isaLSE2)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : InvS := fun lbl lsize s c fs =>
  (lbl = L0 ∧ lsize = ls0 ∧ inv0 s c fs) ∨
    ∃ l b n, L0 l = none ∧ AllocLand ar.heap ar.cells b n ∧ lbl = upd L0 l b ∧ lsize = updN ls0 l n ∧
      inv1 l b n s c fs

/-! ## Rows under a larger allocation fragment -/

/-- **A row under a memory side with a larger allocation fragment**: `ms'`
is `ms` but for `xa`, which contains `ms.xa`. -/
theorem Out.mono_xa {lbl : Lbl} {ms ms' : MemSide isaLSE2} {X : Frag isaLSE2} {s : State} {c : Ctl}
    (h : Out p lbl ms X s c) (he : ms' = { ms with xa := ms'.xa })
    (hxa : ∀ l b n s c, ms.xa l b n s c → ms'.xa l b n s c) : Out p lbl ms' X s c := by
  rw [he]
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr hx
  | choice P t he hs hx => exact .choice P t he hs hx
  | load kl A g x a e ty w he ht hev hv hx htag => exact .load kl A g x a e ty w he ht hev hv hx htag
  | store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag =>
    exact .store kr A V s' x a b e ty tb w wb he ht hev hv hevb hvb hx htag
  | rtStore kr L V s' c' he hrt hm hG hr hx => exact .rtStore kr L V s' c' he hrt hm hG hr hx
  | rtLoad kl L g c' he hrt hm hr hx => exact .rtLoad kl L g c' he hrt hm hr hx
  | rtRmw k L op g c' he hrt hm hr hx => exact .rtRmw k L op g c' he hrt hm hr hx
  | sys K call hK ha hd hok hx => exact .sys K call hK ha hd hok hx
  | holdLoad kl A g x sa u v e he hx hA hh hX => exact .holdLoad kl A g x sa u v e he hx hA hh hX
  | xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he hx hA hh hev hv hX
  | ctrRmw k op g x a τ e ta ws n he hrt hm ht hev hn hh hop hX =>
    exact .ctrRmw k op g x a τ e ta ws n he hrt hm ht hev hn hh hop hX
  | alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu hX =>
    exact .alloc s' A x a τ e ta ws k wold old us he ht hev hk hh hold hA hc hu fun l ini hl =>
      hxa _ _ _ _ _ (hX l ini hl)
  | emit K buf n Pw Qw hK ha hd h0 hb hr hq => exact .emit K buf n Pw Qw hK ha hd h0 hb hr hq

/-- `Out.mono_xa` at the frames. -/
theorem OutS.mono_xa {lbl : Lbl} {ms ms' : List TermRun.Frame → MemSide isaLSE2} {X : FragS isaLSE2} {s : State}
    {c : Ctl} {fs : List TermRun.Frame} (h : OutS p lbl ms X s c fs)
    (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : OutS p lbl ms' X s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (Out.mono_xa h (he fs₁) (hxa fs₁))
  | frame s' c' fs' he' hr hx => exact .frame s' c' fs' he' hr hx

/-! ## The per-pair facts -/

/-- **The per-pair facts with allocation** at the frames `fs` of a thread
state `s` paired with `c`, at the placement `lbl`, `lsize`, over the
fragment `J`: the fields of `SFactsS` but `noAlloc` and `abortOk`, and
- `wr`: at every pair a frame run reaches, off a system call, the arena's
  write obligation, the counter's add landing in `PendA p J`;
- `zero`: at a buffer allocation a frame run reaches, its type passes the
  zero check;
- the abort phase `Ab`: at an abort site the `writeErr` case in `Ab`, the
  overflow case or the heap case (`HeapAbortObl`), with the abort status at
  an `exit_group` (`abortOk`); off `Ab`, no instruction (`abInstr`) and no
  take (`abTake`) enters it, and a system call enters it only as a refused
  `write` (`abSys`).

`Dt` and `Ab` default to false (no `write`, no abort phase). -/
structure SFactsA (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (rS : Range) (Tk : State → Prop) (ar : Arena) (J : InvS) (lbl : Lbl) (lsize : Lsize) (s : State)
    (c : Ctl) (fs : List TermRun.Frame) (Dt : State → Prop := fun _ => False)
    (Ab : State → Prop := fun _ => False) : Prop where
  noRet : fs = [] → ∀ a, c.term ≠ .ret a
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : PlacedSE Λ lbl s c fs
  svc : abi.atSys s = true → ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  ownRun : ∀ c₁ fs₁ c₂ fs₂, FrameRun p (c₁, fs₁) (c₂, fs₂) → ((c₁ = c ∧ fs₁ = fs) ∨ (c₂ = c ∧ fs₂ = fs)) →
    own s fs₂ = own s fs₁
  ownInstr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → OwnTree (own · fs') (own s fs') tree
  ownSys : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
      own s' fs' = own s fs'
  ownTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, own (abi.skip (abi.setDmem s m)) fs = own s fs
  site : ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false ∧
      Kernel.siteRange abi s = rS ∧ rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool
  tkTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, Tk (abi.skip (abi.setDmem s m))
  tkInstr : Kernel.siteAt abi μ s = none → abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  tkSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : Tk s → Owned Λ rS s
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s
  wr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
    WrOkA ar lbl lsize (msOfA Λ μ rd G own ar J lbl lsize fs') (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c'
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true
  abortOk : ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  abInstr : ¬ Ab s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  abSys : ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  abTake : ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))

section AbFalse

variable {μ : Marks} {s : State} {c : Ctl} {fs : List TermRun.Frame} {cells ctr : Nat}

/-- `SFactsA.abInstr` with no abort phase. -/
theorem abInstr_false : ¬ (fun _ : State => False) s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ (fun _ : State => False) s') :=
  fun _ _ tree _ => (allInv_true tree).mono fun _ _ h => h

/-- `SFactsA.abSys` with no abort phase. -/
theorem abSys_false : ¬ (fun _ : State => False) s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
      (fun _ : State => False) s' → ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r :=
  fun _ _ _ _ _ _ h => h.elim

/-- `SFactsA.abTake` with no abort phase. -/
theorem abTake_false : ¬ (fun _ : State => False) s → ∀ a, μ.site .take = some a → pcOf s = a →
    ∀ m, ¬ (fun _ : State => False) (abi.skip (abi.setDmem s m)) :=
  fun _ _ _ _ _ h => h

/-- `SFactsA.abortOk` with no abort phase, from `SFactsS.abortOk`'s form. -/
theorem abortOk_false
    (h : ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨ (k = .heap ∧ HeapAbortObl cells ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ (fun _ : State => False) s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortObl cells ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  fun k a ha hpc => let ⟨hk, hv⟩ := h k a ha hpc; ⟨.inr hk, hv⟩

end AbFalse

/-! ## The obligations -/

/-- **The consumer's obligations from two segment levels**: the
post-allocation family (`h1`, no further allocation, stated first) and the
pre-allocation segment (`h0`, its allocation landing in the family), the
take of `rS` at `a` their outside move, every pair of either level carrying
`SFactsA` at its placement over `I2` (`hW0`, at the pairs of `inv0`, and
`hW1`): `I2` is a fragment with
`NodesA`, `TakePathS`, `AbortPathS` at the phase `Ab`, and every fragment
pair at a `write` in `Dt` (`WrInS`). -/
theorem inst_of_segWA2 {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64}
    {W0 inv0 : FragS isaLSE2} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt Ab : State → Prop}
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeK a rS) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeK a rS) p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsA Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 s c fs Dt Ab)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsA Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab) :
    NodesA Λ p μ rd G own ar (I2 ar L0 ls0 inv0 inv1) ∧ TakePathS Λ p μ (I2 ar L0 ls0 inv0 inv1) rS Tk ∧
      AbortPathS μ (I2 ar L0 ls0 inv0 inv1) Ab ar.cells ar.ctr ∧ WrInS (I2 ar L0 ls0 inv0 inv1) Dt := by
  have hF : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs →
      SFactsA Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs Dt Ab := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩)
    · exact hW0 s c fs hi (h0 s c fs hi).1
    · exact hW1 l b n s c fs hl hland (h1 l b n hl hland s c fs hi).1
  have hR : ∀ lbl lsize s c fs, IRun p (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsA Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c₀ fs₀ Dt Ab ∧
        FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  -- either level's rows off the take site, under the memory side over `I2`
  have hOut : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → (∀ s', ¬ TakeK a rS s s') →
      OutS p lbl (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize)
        (Pend p (I2 ar L0 ls0 inv0 inv1 lbl lsize)) s c fs := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩) hk
    · exact ((h0 s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ h => .inl ⟨rfl, rfl, h⟩
    · refine (OutS.mono_xa ((h1 l b n hl hland s c fs hi).2.1 hk) (fun _ => rfl)
        fun _ _ _ _ _ _ h => h.2.elim).mono fun _ _ _ h => h.mono fun _ _ _ h => ?_
      exact .inr ⟨l, b, n, hl, hland, rfl, rfl, h⟩
  -- an `Out` row at every fragment state off a system call (the take site's `nop`)
  have hRow : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs →
      ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ := by
    intro lbl lsize s c fs hi
    have hdone : ∀ s', isaLSE2.exec s = some (.done s') →
        ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ :=
      fun s' he => ⟨c, msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize fs, fun _ _ => True, rfl,
        .silent s' c he (.refl c) trivial⟩
    by_cases hpc : pcOf s = a.toBitVec.toNat
    · obtain ⟨-, ⟨sz, hcn⟩, -⟩ := (hF lbl lsize s c fs hi).site _ hμ hpc
      exact hdone _ (Kraken.Promising.Lower.A64.exec_nop hcn)
    · have hk : ∀ s', ¬ TakeK a rS s s' := fun s' hk => hpc (pcOf_eq_iff.mpr (TakeK.pc hk))
      cases hOut lbl lsize s c fs hi hk with
      | pre c₁ fs₁ _ h => exact ⟨c₁, _, _, rfl, h⟩
      | frame s' _ _ he _ _ => exact hdone s' he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).wrTail⟩
  -- `NodesA`
  · intro lbl lsize s c fs hi hoff
    exact hOut lbl lsize s c fs hi fun s' hk => hoff _ hμ (pcOf_eq_iff.mpr (TakeK.pc hk))
  · exact fun lbl lsize s c hi => (hF lbl lsize s c [] hi).noRet rfl
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.cell c fs hr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).noSite
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).mapped
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).place
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).svc
  · rintro lbl lsize s c fs c' fs' hr (hi | hi)
    · exact (hF _ _ _ _ _ hi).ownRun c fs c' fs' hr (.inl ⟨rfl, rfl⟩)
    · exact (hF _ _ _ _ _ hi).ownRun c fs c' fs' hr (.inr ⟨rfl, rfl⟩)
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.ownInstr c fs hr
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.ownSys c fs hr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).ownTake
  · intro lbl lsize s c fs hi hns t mem outs o hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK, hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀
    exact ((hF _ _ _ _ _ hi₀).wr c fs hr hns).ctrRow hout hK hns hst hstep ho hW
  · intro lbl lsize s c fs hi hns t mem outs o L hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK, hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀
    exact ((hF _ _ _ _ _ hi₀).wr c fs hr hns).arena_of hout hK hns hst hstep ho hW
  · intro lbl lsize s c fs hi x a' τ e ht
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact zero_of_zeroOkTy (hf.zero c fs hr x a' τ e ht)
  -- `TakePathS`
  · intro lbl lsize s c fs hi a' ha' hpc
    obtain ⟨h1', h2, h3, h4, h5, h6, h7⟩ := (hF lbl lsize s c fs hi).site a' ha' hpc
    refine ⟨h1', h2, h3, h4, h5, h6, h7, fun pm => ?_⟩
    have hk : TakeK a rS s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    have htk := (hF lbl lsize s c fs hi).tkTake a' ha' hpc (Kernel.copyRange pm (abi.dmem s) rS)
    rcases hi with ⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h0 s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inl ⟨rfl, rfl, hi'⟩, htk⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h1 l b n hl hland s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inr ⟨l, b, n, hl, hland, rfl, rfl, hi'⟩, htk⟩
  · exact fun lbl lsize s c fs hi hn => (hF lbl lsize s c fs hi).tkInstr hn
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).tkSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).owned
  -- `AbortPathS` at the phase `Ab`
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abortOk
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abInstr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abTake

/-- **`WriteNoPromA` from a closed tail** (`writeNoPromS_of_wrIn` with the
arena): in `PreSA` thread 0 is certified; at a `write` its state is in `Dt`
(`WrInS`), which the certifying run never leaves keeping the promise set
(`hs`), so the set is empty (`prom_nil_of_closed`). -/
theorem writeNoPromA_of_wrIn {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {G : Loc → Val → Prop}
    {own : OwnS} {I : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {ar : Arena} {Dt : State → Prop}
    (h : WrInS I Dt)
    (hs : ∀ x (p q : Thread isaLSE2 × Memory), Dt p.1.st →
      ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 p q → Dt q.1.st ∧ q.1.prom = p.1.prom) :
    WriteNoPromA Λ P p G own I rS Tk μ ar := by
  rintro t s th ⟨th', _, _, lbl, lsize, _, _, _, _, hth, -, -, -, -, hc, -, -, -, hI, -⟩ hth1 hat ⟨fd, buf, n, hw⟩
  rw [hth] at hth1
  cases Option.some.inj (show some th' = some th from congrArg (·[0]?) hth1)
  exact prom_nil_of_closed (Q := fun x => Dt x.1.st) (t := th) (mem := t.1.mem)
    (fun x y hx hs' => hs _ x y hx hs') (h _ _ th.st _ _ hI hat fd buf n hw) hc

end Spike.Lib.A64ConsumerA
