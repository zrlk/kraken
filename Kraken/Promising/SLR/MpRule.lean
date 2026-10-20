/-
The two rules of MP: the writer's `ThreadRuleRX` (`mpRuleW`, invariant
`InvXW`, which may speak about the writer's own pending flag promise) and the
reader's plain `ThreadRuleR` (`mpRuleR`, invariant `InvR`), both with the
shared postcondition `MpPost P rd`, and their `NPSafe` corollaries.

- Writer: `InvW` and `OwnPendW` at the extension (`invW_env`,
  `ownPendW_transport`); away from position 3 no own promise is pending
  (`noPendW`), so the cells in `CellW` form lift (`mp_lift`). At the end
  (position 4) it holds all of `W`: the left disjunct of `MpPost`.
- Reader: the environment only grows the memory, so `Seen` survives
  (`EnvExt.read?`) and `WorldR` survives `Ghost.Le` (the acquire table
  grows by prefix). At the end, under the clean flag, `W4 = 1`: the right
  disjunct of `MpPost` with its acquire id. Its prepay obligation is vacuous:
  none of its instructions stores (`Thread.RelFulfils` fails on every tree).

`WorldR.mono` is in `SLR/MpSpec.lean` (moved unchanged).
-/
import Kraken.Promising.SLR.MpWriter
import Kraken.Promising.SLR.MpReader
import Kraken.Promising.SLR.MpSpec

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

variable [hw : Executable.ValidLayout (layout mpWriter)]

/-- Away from position 3 the writer has no own pending promise. -/
theorem noPendW {P : Params} {tid : Nat} {c : Config isa} {r : Res} {g : Ghost} {t : Thread isa}
    (hOP : OwnPendW P tid c r g) (ht : c.threads[tid]? = some t) {i : Nat}
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) (hp : AtPos mpWriter t.st i) (h3 : i ≠ 3) :
    ∀ ts ∈ t.prom, ts ∉ g.pend :=
  fun ts hts hpd => h3 (atPosW_eq_3 hi (hOP t ht ts hts hpd).1 hp)

/-- **`done`**: a halted writer is at the end, holding all of `W`. -/
theorem invW_done {P : Params} {tid rd : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvW P tid cl c r g) (hd : c.Done tid) : MpPost P rd c r g := by
  obtain ⟨-, t, ht, hF, i, hp, hph, -⟩ := h
  obtain ⟨t', ht', hhalt, -⟩ := hd
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hnone : isa.exec t.st = none := by simpa [Thread.halted] using hhalt
  rcases PhaseW.pos hph with rfl | rfl | rfl | rfl | rfl
  · rw [exec_w_mov2 t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_w_str t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hnone; cases hnone
  · rw [exec_w_mov3 t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_w_stlr t.st (hF.at hp (by decide)) hF.x0 hF.df] at hnone; cases hnone
  · exact .inl hph

/-- **The writer's rule** (`ThreadRuleRX`). -/
def mpRuleW (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) : ThreadRuleRX (I := isa) A (MpPost P rd) tid where
  Inv := InvXW P tid
  done := fun h he hle _ hd => invW_done (invW_env h.1 he hle) hd
  wp := fun {cl} {c₀} {c} {r} {g₀} {g} rF t tree h he hle ht hex E hinv _ hnp => by
    have hOP := ownPendW_transport h he ht hnp
    obtain ⟨hW, t', ht', hF, i, hp, hph, hpp⟩ := invW_env h.1 he hle
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    have hpos := PhaseW.pos hph
    have hno := noPendW hOP ht hpos hp
    rcases hpos with rfl | rfl | rfl | rfl | rfl
    · exact mp_lift rF t tree ht E hinv (hno (by decide))
        (wpW_mov2 rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact mp_lift rF t tree ht E hinv (hno (by decide))
        (wpW_str hA rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact mp_lift rF t tree ht E hinv (hno (by decide))
        (wpW_mov3 rF t tree hW ht hF hp hph hex E hinv (hno (by decide)))
    · exact wpW_stlr hL rF t tree hW ht hF hp hph hpp hex E hinv hOP
    · rw [exec_end_w hF hp] at hex; cases hex
  prepay := fun rF t₁ w h he hle ht E hinv hnp hrel => mp_prepay hL hA' rF t₁ w h he hle ht E hinv hnp hrel

/-- **The writer is non-promisingly safe** at every clean flag. -/
theorem mpW_npsafe (P : Params) (A : Arch) (tid rd : Nat) (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt)
    (hA' : A.plainStore ≠ .rel) (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvXW P tid cl c r g) : NPSafe (model isa) A (MpPost P rd) tid n m cl c r g :=
  NPSafe.of_ruleRX (mpRuleW P A tid rd hL hA hA') n m cl c r g h

end Writer

/-! ## The reader -/

omit layout in
theorem seen_of_envExt {P : Params} {tid : Nat} {c c₁ : Config isa} (he : EnvExt tid c c₁) {V : View}
    (h : Seen P c.mem V) : Seen P c₁.mem V := by
  obtain ⟨ts, v, hrd, hv, hts⟩ := h
  exact ⟨ts, v, EnvExt.read? he hrd, hv, hts⟩

/-- **`env`** for the reader. -/
theorem invR_env {P : Params} {tid : Nat} {cl : Prop} {c c₁ : Config isa} {r : Res} {g g₁ : Ghost}
    (h : InvR P tid cl c r g) (he : EnvExt tid c c₁) (hle : g.Le g₁) : InvR P tid cl c₁ r g₁ := by
  obtain ⟨hW, t, ht, hF, i, hp, hph⟩ := h
  obtain ⟨ps, ht₁, -⟩ := he.2.2 t ht
  refine ⟨hW.mono hle, _, ht₁, hF, i, hp, ?_⟩
  have hpos := PhaseR.pos hph
  revert hph
  rcases hpos with rfl | rfl | rfl | rfl <;> simp only [PhaseR]
  · exact id
  · exact fun ⟨h1, h2⟩ => ⟨h1, fun hz => seen_of_envExt he (h2 hz)⟩
  · exact fun ⟨h1, h2⟩ => ⟨h1, seen_of_envExt he h2⟩
  · exact fun ⟨⟨V, h1⟩, h2⟩ => ⟨⟨V, seen_of_envExt he h1⟩, h2⟩

section Reader

variable [hr : Executable.ValidLayout (layout mpReader)]

/-- **`done`**: a halted reader is at the end; under the clean flag it has
loaded `1` and keeps its acquire id. -/
theorem invR_done {P : Params} {tid : Nat} {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvR P tid cl c r g) (hcl : cl) (hd : c.Done tid) : MpPost P tid c r g := by
  obtain ⟨⟨-, hacq⟩, t, ht, hF, i, hp, hph⟩ := h
  obtain ⟨t', ht', hhalt, -⟩ := hd
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hnone : isa.exec t.st = none := by simpa [Thread.halted] using hhalt
  rcases PhaseR.pos hph with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar t.st (hF.at hp (by decide)) hF.x0 hF.df] at hnone; cases hnone
  · rw [exec_r_cbz t.st (hF.at hp (by decide))] at hnone; cases hnone
  · rw [exec_r_ldr t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hnone; cases hnone
  · simp only [PhaseR] at hph
    obtain ⟨⟨V, ts, v, hrd, hv, -⟩, hx4⟩ := hph
    exact .inr ⟨⟨⟨t, ht, hx4 hcl⟩, ts, v, hrd, hv⟩, hacq⟩

/-- No reader instruction fulfils a promise with a release store: none
stores. -/
theorem reader_not_relFulfils {P : Params} {A : Arch} {tid : Nat} {t : Thread isa} {mem : Memory} {ts : Time}
    {i : Nat} {st : State} (hF : FrameR P st) (hp : AtPos mpReader st i) (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4)
    (h : t.RelFulfils A tid ts mem) (hst : t.st = st) : False := by
  subst hst
  obtain ⟨tree, hex, hrf⟩ := h
  rcases hi with rfl | rfl | rfl | rfl
  · rw [exec_r_ldar t.st (hF.at hp (by decide)) hF.x0 hF.df] at hex; cases hex
    simp [EvTree.RelFulfils] at hrf
  · rw [exec_r_cbz t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfils] at hrf
  · rw [exec_r_ldr t.st (hF.at hp (by decide)) hF.x1 hF.dd] at hex; cases hex
    simp [EvTree.RelFulfils] at hrf
  · rw [exec_end_r hF hp] at hex; cases hex

/-- **The reader's rule** (`ThreadRuleR`). -/
def mpRuleR (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) : ThreadRuleR (I := isa) A (MpPost P tid) tid where
  Inv := InvR P tid
  env := invR_env
  done := fun h hcl hd => invR_done h hcl hd
  wp := fun {cl} {c} {r} {g} _ rF t tree h _ ht hex _ _ _ _ => by
    obtain ⟨hW, t', ht', hF, i, hp, hph⟩ := h
    rw [ht] at ht'
    obtain rfl : t = t' := Option.some.inj ht'
    rcases PhaseR.pos hph with rfl | rfl | rfl | rfl
    · exact wpR_ldar hA1 hA2 rF t tree hW ht hF hp hph hex
    · exact wpR_cbz rF t tree hW ht hF hp hph hex
    · exact wpR_ldr rF t tree hW ht hF hp hph hex
    · rw [exec_end_r hF hp] at hex; cases hex
  prepay := fun _ _ t₁ _ h _ ht _ _ _ hrel => by
    obtain ⟨-, t, ht', hF, i, hp, hph⟩ := h
    rw [ht] at ht'
    obtain rfl : t₁ = t := Option.some.inj ht'
    exact (reader_not_relFulfils hF hp (PhaseR.pos hph) hrel rfl).elim

/-- **The reader is non-promisingly safe** at every clean flag. -/
theorem mpR_npsafe (P : Params) (A : Arch) (tid : Nat) (hA1 : (A.loadKind .acq).isAcquire = true)
    (hA2 : (A.loadKind .acq == .plain) = false) (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvR P tid cl c r g) : NPSafe (model isa) A (MpPost P tid) tid n m cl c r g :=
  NPSafe.of_ruleR (mpRuleR P A tid hA1 hA2) n m h

end Reader

end Kraken.Promising.SLR.Mp
