/-
**The runtime's transfer and abort sites of code at another base, or with
a tail appended** (x86-64; `Scc/Cert/Rt/PhasesX64.lean`'s `sitesOf`,
`okPcOf`): the sites' addresses move with the base, and a tail appended
after the cells leaves them where they were.

- `sitesBy_map`: the sites resolved by a resolver followed by a map;
- `sitesOf_shift`, `okPcOf_shift`: at the base moved by `δ`;
- `sitesOf_append_of`, `okPcOf_append_of`: with a tail appended, the sites
  resolving in the cells.
-/
import Scc.Cert.Rt.PhasesX64
import Spike.Lib.X64TextTail

namespace Spike.Lib.X64PhTail

open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (sitesBy sitesOf okPcOf siteLabels)

/-- `mapM` of a resolver followed by a map is the map of the `mapM`. -/
private theorem mapM_map_option {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ xs : List α, xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g)
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, mapM_map_option f g xs]
    cases f x <;> cases xs.mapM f <;> rfl

/-- **The sites resolved by a resolver followed by a map** are the map of
the sites. -/
theorem sitesBy_map (code : String → Option Nat) (g : Nat → Nat) (Λ : Scc.Sem.Layout) :
    sitesBy (fun l => (code l).map g) Λ = (sitesBy code Λ).map (List.map g) :=
  mapM_map_option code g _

/-- **The sites at the base moved by `δ`** are the sites moved by `δ`. -/
theorem sitesOf_shift (lo δ : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) :
    sitesOf (lo + δ) cells Λ = (sitesOf lo cells Λ).map (List.map (· + δ)) := by
  unfold sitesOf
  rw [show codeLabel (lo + δ) cells = fun l => (codeLabel lo cells l).map (· + δ) from
    funext (Spike.Lib.X64TextTail.codeLabel_shift lo δ cells)]
  exact sitesBy_map _ _ Λ

/-- `mapM` of two resolvers agreeing wherever the first resolves. -/
private theorem mapM_some_congr {α β : Type} {f g : α → Option β} (hfg : ∀ x b, f x = some b → g x = some b) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.mapM g = some ys
  | [], _, h => h
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some b =>
      cases hxs : xs.mapM f with
      | none => rw [hx, hxs] at h; cases h
      | some bs =>
        rw [hx, hxs] at h
        rw [hfg x b hx, mapM_some_congr hfg hxs]
        exact h

/-- **The sites with a tail appended**, every site resolving in the cells. -/
theorem sitesOf_append_of {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {ss : List Nat}
    (T : List (Directive × Nat)) (h : sitesOf lo cells Λ = some ss) : sitesOf lo (cells ++ T) Λ = some ss :=
  mapM_some_congr (fun _ _ ha => Spike.Lib.X64TextTail.codeLabel_append_of T ha) h

/-- **The pcs off the sites at the base moved by `δ`**: a pc moved by `δ`
is off the moved sites as the pc is off the sites. -/
theorem okPcOf_shift {lo δ : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {pc : Nat} :
    okPcOf (lo + δ) cells Λ (pc + δ) = okPcOf lo cells Λ pc := by
  unfold okPcOf
  rw [sitesOf_shift]
  cases sitesOf lo cells Λ with
  | none => rfl
  | some ss =>
    simp only [Option.map_some]
    congr 1
    induction ss with
    | nil => rfl
    | cons a ss ih =>
      simp only [List.map_cons, List.contains_cons, ih]
      congr 1
      cases h : pc == a <;> simp_all

/-- **The pcs off the sites with a tail appended**, every site resolving in
the cells. -/
theorem okPcOf_append_of {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {ss : List Nat}
    (T : List (Directive × Nat)) (h : sitesOf lo cells Λ = some ss) (pc : Nat) :
    okPcOf lo (cells ++ T) Λ pc = okPcOf lo cells Λ pc := by
  unfold okPcOf
  rw [sitesOf_append_of T h, h]

end Spike.Lib.X64PhTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64PhTail.sitesOf_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64PhTail.sitesOf_shift

/-- info: 'Spike.Lib.X64PhTail.sitesOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64PhTail.sitesOf_append_of

/-- info: 'Spike.Lib.X64PhTail.okPcOf_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64PhTail.okPcOf_shift

/-- info: 'Spike.Lib.X64PhTail.okPcOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64PhTail.okPcOf_append_of
