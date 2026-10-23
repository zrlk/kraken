import WeakCore.CoreTyping
import WeakCore.TermRun
import WeakCore.TermClose
import WeakCore.TermTv
import WeakCore.TermCkB

/-!
# TermSound — T3: the judgement against the machine

A runtime frame is paired with a valuation `ρ` of the block's index variables
and an interpretation `η` of its type variables.  The invariant
`FInv ρ η cx env` says that `ρ` satisfies every fact in the static context and
that every variable's words realise its type (`VR`) and have the length its
runtime type's layout says (`ShapeC`).

**Type variables are interpreted semantically** (T3b design option 1):
`η k` is a relation on (runtime type, words).  At a call, the callee's `η` is
the caller's `VR` at the caller's static type arguments, so a block checked
once at `α : κ` is never re-typed: row 18's polymorphic-instance lemma becomes
a substitution lemma for `VR`.

Stage T3a: index soundness, integer fragment (P1 + P4 for `atom`, `add`,
`sub`, `nameI`, `rem`, `ifeq`, `parity`).

Stage T3b-1 (this revision): first-order values whose runtime shape is built
in the frame.
* `VR` constrains integers, pairs (with the runtime split point) and index
  existentials; `VR_shift`, `VR_tyEq` (`TyEqS`), `VR_sub` (`SubS`) and
  `VR_instT` (index instantiation) are its structural lemmas.
* `accs_width`: the load/store layout of a type has exactly `width` words.
  This is what keeps `ShapeC` through `unpack` of a coupled package.
* P1 + P4 for `pair`, `pack` (integer bodies), `unpack`; P1 for `split` (its
  P4 needs the runtime left component to have a layout — shape agreement).

Deferred to T3b-2: `pack` of bodies holding pairs, code values and calls.  All
need runtime types to agree in shape with the instantiated static types.

Stage 24e: type existentials (`packT`, `unpackT`).  T3c-2 (option
B): every type variable carries a closed witness (`TEnv.wit`); `VR`
realises a package's body with a variable whose witness is some closed `s` and
whose relation is empty, which `guardT` keeps where `VR` reads only witnesses
(`VR_relsG`).  A code value's static signature closes (`TermClose.cl`) to its
block's; `VR_close` turns that into the transfer of `VR` (`VR_code`).  A code word keeps its block's runtime signature, so
shapes read signatures through `sig` (pointees `Unit`, variables `tvar 0`);
`sig_pack` says the witness is invisible there.  `unpackT` runs the body with
`Unit` for the witness (`substTs_substT_unit`, `pushT_FInv`); P1 + P4 are
`pure_pres`/`pure_progress` (`packT`) and `tstep_unpackT`.

T3c-3: `TEnv` carries the store typing Σ (`sto`: label →
`Cell`, the closed type of the contents and the owner) and the running thread
(`tid`).  `VR` at `ptr μ u` / `ptrOpt` / `loc`: the word is a location whose
cell is in Σ, holds exactly `cl ρ η.wit 0 0 u` (at the locative's offset,
`AtOff`), and agrees with the mode (`ModeOK`).  `VR_mono`: a larger Σ keeps `VR`.
-/

set_option linter.unusedSimpArgs false

namespace TermSound
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv

/-! ## §1 Valuations and shifts -/

/-- `ρ` with `w` inserted at position `c`. -/
def vins (c w : Nat) (ρ : Nat → Nat) : Nat → Nat :=
  fun k => if k < c then ρ k else if k = c then w else ρ (k - 1)

/-- `ρ` after a `push`: `w` at 0. -/
abbrev vcons (w : Nat) (ρ : Nat → Nat) : Nat → Nat := vins 0 w ρ

theorem ev_shift (c w : Nat) (ρ : Nat → Nat) : ∀ i : Idx, ev (vins c w ρ) (i.shift c) = ev ρ i
  | .lit n => by simp [Idx.shift, ev]
  | .var k => by
      simp only [Idx.shift]
      split
      · simp only [ev, vins]
        split
        · omega
        · split
          · omega
          · simp
      · simp only [ev, vins]
        split
        · rfl
        · omega
  | .add i j => by simp [Idx.shift, ev, ev_shift c w ρ i, ev_shift c w ρ j]
  | .sub i j => by simp [Idx.shift, ev, ev_shift c w ρ i, ev_shift c w ρ j]
  | .smul n i => by simp [Idx.shift, ev, ev_shift c w ρ i]

theorem vins_succ (c w w' : Nat) (ρ : Nat → Nat) :
    vins (c + 1) w (vcons w' ρ) = vcons w' (vins c w ρ) := by
  funext k
  simp only [vins]
  by_cases h0 : k = 0
  · subst h0; simp
  · have : k - 1 < c ↔ k < c + 1 := by omega
    by_cases h1 : k < c + 1
    · simp [h1, h0]; omega
    · by_cases h2 : k = c + 1
      · subst h2; simp
      · simp [h1, h2, h0]
        split
        · omega
        · split
          · omega
          · have : k - 1 ≠ c := by omega
            simp [this]

theorem vcons_zero (w : Nat) (ρ : Nat → Nat) : vcons w ρ 0 = w := by simp [vins]
theorem vcons_succ (w : Nat) (ρ : Nat → Nat) (k : Nat) : vcons w ρ (k + 1) = ρ k := by
  simp [vins]

theorem vcons_eta (ρ : Nat → Nat) : vins 0 (ρ 0) (fun k => ρ (k + 1)) = ρ := by
  funext k; cases k <;> simp [vins]

theorem ev_shiftN (w : Idx) : ∀ (d : Nat) (ρ : Nat → Nat), ev ρ (shiftN d w) = ev (fun k => ρ (k + d)) w
  | 0, ρ => by simp [shiftN]
  | d + 1, ρ => by
      have h := ev_shift 0 (ρ 0) (fun k => ρ (k + 1)) (shiftN d w)
      rw [vcons_eta] at h
      simp only [shiftN]
      rw [h, ev_shiftN w d] <;> rfl

/-- Instantiating index binder `d` by `w` is evaluating with `w`'s value
inserted at `d`. -/
theorem ev_instI (w : Idx) (d : Nat) (ρ : Nat → Nat) :
    ∀ i : Idx, ev ρ (instI [w] d i) = ev (vins d (ev (fun k => ρ (k + d)) w) ρ) i
  | .lit n => by simp [instI, ev]
  | .var k => by
      simp only [instI]
      by_cases h1 : k < d
      · simp [h1, ev, vins]
      · by_cases h2 : k = d
        · subst h2; simp [ev, vins, ev_shiftN]
        · have h3 : [w][k - d]? = none := by simp; omega
          simp [h1, h3, ev, vins, h2]
  | .add i j => by simp [instI, ev, ev_instI w d ρ i, ev_instI w d ρ j]
  | .sub i j => by simp [instI, ev, ev_instI w d ρ i, ev_instI w d ρ j]
  | .smul n i => by simp [instI, ev, ev_instI w d ρ i]

/-! ## §2a Shapes: what the value relation reads from a runtime type

Runtime types are built in many places (`pack`, `enter`, `load`, `region`, …)
and differ from each other in index terms: a loaded integer is `Int`, not
`Int(i)`; a region's pointer mentions `lit 0`, not the region variable.  None
of that is read by the machine.  `shp` keeps exactly what the value relation
inspects — pairs, index packages, fixed-width and lane types —
and, everywhere else, only the layout's word count.  Two runtime types with
the same shape are interchangeable for `VR` (`VR_agree`), and a type
variable's meaning `η k` is a relation on shapes, so it cannot tell them apart
either. -/

/-- The word count of a runtime layout. -/
def wc (t : Ty) : Option Nat := (accs t).map nWords

/-! Skeletons (§2d) are defined here: shapes and `lnorm` read them. -/

def skelM : Mode → Mode
  | .rgn _ => .rgn (.lit 0)
  | μ => μ

/-- A refinement, except that a refined integer is an integer: integer
operations re-type their results (`nameI` gives `Int(n)` to a refined source's
words), and nothing matches on an integer's refinement. -/
def rf : Ty → Ty
  | .int => .int
  | t => .refine t .tt

def skel : Ty → Ty
  | .intS _ => .int
  | .prod a b => .prod (skel a) (skel b)
  | .sum a b => .sum (skel a) (skel b)
  | .code a b => .code (skel a) (skel b)
  | .array _ t => .array (.lit 0) (skel t)
  | .ptr μ t => .ptr (skelM μ) (skel t)
  | .ptrOpt μ t => .ptrOpt (skelM μ) (skel t)
  | .loc μ t => .loc (skelM μ) (skel t)
  | .word _ P => .word (.lit 0) P
  | .tok _ _ => .tok (.lit 0) none
  | .word2 _ P => .word2 (.lit 0) P
  | .tok2 _ P _ _ => .tok2 (.lit 0) P (.lit 0) (.lit 0)
  | .epair _ P => .epair (.lit 0) P
  | .tokE _ P _ => .tokE (.lit 0) P (.lit 0)
  | .share _ => .share (.lit 0)
  | .cap s _ => .cap s (.lit 0)
  | .mu t => .mu (skel t)
  | .tex κ t => .tex κ (skel t)
  | .iall t => .iall (skel t)
  | .iex t => .iex (skel t)
  | .refine t _ => rf (skel t)
  | t => t

/-- What anything can read of a runtime signature (24e): the type with every
pointee `Unit` and every type variable `tvar 0`.  No layout reads a pointee
(`info` at a reference is one word whatever it points to) or a variable's
index (at `Ty.top` every variable is of unknown width).  A closure's code
word keeps its block's signature, `Code(A × Ptr Env) B`, while the package's
view is `Code(A × Ptr α) B`: they differ only where `er` erases.  (T3d-1)
Tokens, epoch tokens and shares have no words and are `Unit` to a signature:
a runtime binding may hold `Unit` where the static type has one (`etok`). -/
def er : Ty → Ty
  | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ => .unit
  | .prod a b => .prod (er a) (er b)
  | .sum a b => .sum (er a) (er b)
  | .code _ _ => .code .unit .unit   -- (T3c-5a-4) a code value is one word; its signature is static
  | .array i t => .array i (er t)
  | .ptr μ _ => .ptr μ .unit
  | .ptrOpt μ _ => .ptrOpt μ .unit
  | .loc μ _ => .loc μ .unit
  | .tvar _ => .tvar 0
  | .mu t => .mu (er t)
  | .tex κ t => .tex κ (er t)
  | .iall t => .iall (er t)
  | .iex t => .iex (er t)
  | .refine t ψ => .refine (er t) ψ
  | t => t

/-- A code value's runtime signature component, as shapes see it. -/
def sig (t : Ty) : Ty := er (skel t)

/-- **Token erasure** (T3d-1, option 1b).  A token, an epoch token or a share
has no words, so the runtime binds `Unit` where the static type has one (a
`cas` or `claim` result, a Keep store's token); `Lay` compares skeletons and
layout forms modulo `etok`.  It does not look under index or type binders
(`iex`, `tex`, `iall`, `mu`): the runtime binds a package or a fold at its
annotation, so nothing differs there, and a coupled package's layout counts
its body's index mentions (`accs`), which erasing a token would change. -/
def etok : Ty → Ty
  | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ => .unit
  | .prod a b => .prod (etok a) (etok b)
  | .sum a b => .sum (etok a) (etok b)
  | .code a b => .code (etok a) (etok b)
  | .array i t => .array i (etok t)
  | .ptr μ t => .ptr μ (etok t)
  | .ptrOpt μ t => .ptrOpt μ (etok t)
  | .loc μ t => .loc μ (etok t)
  | .refine t ψ => .refine (etok t) ψ
  | t => t

/-- **Layout normal form** of a runtime sum (§2a's `Shp.sum`): what the
encoder reads, and nothing `SubS` can change — refinements dropped, integers
unindexed, every pointer arm `Ptr?` to `Unit`, capabilities `Unit`.  It keeps
tiers and arm kinds up to `Ptr ≤ Ptr?`, so decoding at `lnorm` is at least as
permissive as at the runtime type (`decodeArm_mono`). -/
def lnorm : Ty → Ty
  | .intS _ => .int
  | .prod a b => .prod (lnorm a) (lnorm b)
  | .sum a b => .sum (lnorm a) (lnorm b)
  | .code _ _ => .code .unit .unit   -- one word; the signature is static (T3c-5a-4)
  | .array _ _ => .array (.lit 0) .unit
  | .ptr _ _ => .ptrOpt .pub .unit
  | .ptrOpt _ _ => .ptrOpt .pub .unit
  | .loc _ _ => .ptrOpt .pub .unit
  | .word _ P => .word (.lit 0) P
  | .tok _ _ => .unit
  | .word2 _ P => .word2 (.lit 0) P
  | .tok2 _ _ _ _ => .unit
  | .epair _ P => .epair (.lit 0) P
  | .tokE _ _ _ => .unit
  | .share _ => .unit
  | .cap _ _ => .unit
  | .mu t => .mu (lnorm t)
  | .tex κ t => .tex κ (lnorm t)
  | .iall t => .iall (lnorm t)
  | .iex t => .iex (lnorm t)
  | .refine t _ => lnorm t
  | .tvar _ => .tvar 0
  | t => t

@[simp] theorem cst_val (v : WeakMem.Val) : (cst v).val = v := rfl

/-- Two word lists with the same values. -/
abbrev VEq (ws ws' : List Word) : Prop := ws.map (·.val) = ws'.map (·.val)


theorem veq_one {w : Word} {ws' : List Word} (e : VEq [w] ws') : ∃ w', ws' = [w'] ∧ w'.val = w.val := by
  match ws', e with
  | [w'], e => simp [VEq] at e; exact ⟨w', rfl, e.symm⟩
  | [], e => simp [VEq] at e
  | _ :: _ :: _, e => simp [VEq] at e

theorem veq_two {t w : Word} {ws' : List Word} (e : VEq [t, w] ws') :
    ∃ t' w', ws' = [t', w'] ∧ t'.val = t.val ∧ w'.val = w.val := by
  match ws', e with
  | [t', w'], e => simp [VEq] at e; exact ⟨t', w', rfl, e.1.symm, e.2.symm⟩
  | [], e => simp [VEq] at e
  | [_], e => simp [VEq] at e
  | _ :: _ :: _ :: _, e => simp [VEq] at e

/-- (T3c-5c) `w'` has `w`'s value and, if it is a pointer, at least its view:
what a load or a store does to a pointer word (`dataE`), and all that `VR`
asks of views (`ModeOK` at `pub`). -/
def WLe1 (w w' : Word) : Prop := w.val = w'.val ∧ ∀ a g, w.val = .loc a g → w.view ≤ w'.view

def WLe : List Word → List Word → Prop
  | [], [] => True
  | w :: ws, w' :: ws' => WLe1 w w' ∧ WLe ws ws'
  | _, _ => False

theorem WLe1_refl (w : Word) : WLe1 w w := ⟨rfl, fun _ _ _ => Nat.le_refl _⟩

theorem WLe1_trans {a b c : Word} (h1 : WLe1 a b) (h2 : WLe1 b c) : WLe1 a c :=
  ⟨h1.1.trans h2.1, fun x g h => Nat.le_trans (h1.2 x g h) (h2.2 x g (h1.1 ▸ h))⟩

theorem WLe_refl : ∀ ws : List Word, WLe ws ws
  | [] => trivial
  | w :: ws => ⟨WLe1_refl w, WLe_refl ws⟩

theorem WLe_trans : ∀ {a b c : List Word}, WLe a b → WLe b c → WLe a c
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, h1, h2 => ⟨WLe1_trans h1.1 h2.1, WLe_trans h1.2 h2.2⟩
  | [], _ :: _, _, h1, _ => (h1 : False).elim
  | _ :: _, [], _, h1, _ => (h1 : False).elim
  | [], [], _ :: _, _, h2 => (h2 : False).elim
  | _ :: _, _ :: _, [], _, h2 => (h2 : False).elim

theorem WLe.vals : ∀ {ws ws' : List Word}, WLe ws ws' → VEq ws ws'
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [VEq, List.map_cons, h.1.1, h.2.vals]
  | [], _ :: _, h => (h : False).elim
  | _ :: _, [], h => (h : False).elim

theorem WLe.length {ws ws' : List Word} (h : WLe ws ws') : ws.length = ws'.length := by
  have := congrArg List.length h.vals; simpa using this

theorem WLe.take : ∀ (n : Nat) {ws ws' : List Word}, WLe ws ws' → WLe (ws.take n) (ws'.take n)
  | 0, _, _, _ => by simp [WLe]
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, WLe.take n h.2⟩
  | _ + 1, [], _ :: _, h => (h : False).elim
  | _ + 1, _ :: _, [], h => (h : False).elim

theorem WLe.drop : ∀ (n : Nat) {ws ws' : List Word}, WLe ws ws' → WLe (ws.drop n) (ws'.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => WLe.drop n h.2
  | _ + 1, [], _ :: _, h => (h : False).elim
  | _ + 1, _ :: _, [], h => (h : False).elim

theorem WLe.append : ∀ {a a' b b' : List Word}, WLe a a' → WLe b b' → WLe (a ++ b) (a' ++ b')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h1, h2 => ⟨h1.1, WLe.append h1.2 h2⟩
  | [], _ :: _, _, _, h, _ => (h : False).elim
  | _ :: _, [], _, _, h, _ => (h : False).elim

/-- Words without pointers: the views do not matter. -/
theorem WLe_of_vals : ∀ {ws ws' : List Word}, VEq ws ws' → (∀ w ∈ ws, ∀ a g, w.val ≠ .loc a g) → WLe ws ws'
  | [], [], _, _ => trivial
  | w :: ws, w' :: ws', e, h => by
      simp only [VEq, List.map_cons, List.cons.injEq] at e
      exact ⟨⟨e.1, fun a g hw => absurd hw (h w (by simp) a g)⟩,
        WLe_of_vals e.2 (fun x hx => h x (by simp [hx]))⟩
  | [], _ :: _, e, _ => by simp [VEq] at e
  | _ :: _, [], e, _ => by simp [VEq] at e

theorem WLe_one {w : Word} {ws' : List Word} (h : WLe [w] ws') : ∃ w', ws' = [w'] ∧ WLe1 w w' := by
  match ws', h with
  | [w'], h => exact ⟨w', rfl, h.1⟩
  | [], h => exact (h : False).elim
  | _ :: _ :: _, h => exact (h.2 : False).elim

theorem WLe_two {t w : Word} {ws' : List Word} (h : WLe [t, w] ws') :
    ∃ t' w', ws' = [t', w'] ∧ WLe1 t t' ∧ WLe1 w w' := by
  match ws', h with
  | [t', w'], h => exact ⟨t', w', rfl, h.1, h.2.1⟩
  | [], h => exact (h : False).elim
  | [_], h => exact (h.2 : False).elim
  | _ :: _ :: _ :: _, h => exact (h.2.2 : False).elim

/-- A pointer's view bound moves up along `WLe`. -/
theorem WLe_view {ws ws' : List Word} {a : WeakMem.Address} {g : Nat} (h : WLe ws ws')
    (hv : ws.map (·.val) = [.loc a g]) : ∀ f, (∀ w ∈ ws, f ≤ w.view) → ∀ w ∈ ws', f ≤ w.view := by
  match ws, hv with
  | [w], hv =>
    obtain ⟨w', rfl, h1⟩ := WLe_one h
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
    intro f hf x hx
    simp only [List.mem_singleton] at hx; subst hx
    exact Nat.le_trans (hf w (by simp)) (h1.2 a g hv)
  | [], hv => simp at hv
  | _ :: _ :: _, hv => simp at hv

theorem decodeArm_vals {tr : Tier} {as : List Ty} {ws ws' : List Word} {j : Nat} {p : List Word}
    (e : VEq ws ws') (h : decodeArm tr as ws = some (j, p)) :
    ∃ p', decodeArm tr as ws' = some (j, p') ∧ VEq p p' := by
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · obtain ⟨w', rfl, ew⟩ := veq_one e
        simp only [decodeArm] at h ⊢
        rw [ew]
        cases hw : w.val with
        | loc a g =>
            rw [hw] at h
            cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
            | none => simp [h1, bind, Option.bind] at h
            | some pr =>
                simp [h1, bind, Option.bind, pure] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨[{ w' with val := .loc a 0 }], by simp [h1, bind, Option.bind, pure], by simp [VEq]⟩
        | num k =>
            rw [hw] at h
            exact ⟨p, h, rfl⟩
        | _ => rw [hw] at h; simp at h
      · simp [decodeArm] at h
  | wide =>
      rcases ws with _ | ⟨t, _ | ⟨w, _ | ⟨w3, rest⟩⟩⟩
      · simp [decodeArm] at h
      · simp [decodeArm] at h
      · obtain ⟨t', w', rfl, et, ew⟩ := veq_two e
        simp only [decodeArm] at h ⊢
        rw [et]
        cases ht : t.val with
        | num k =>
            rw [ht] at h
            cases h1 : as[k]? with
            | none => simp [h1, bind, Option.bind] at h
            | some a =>
                simp only [h1, bind, Option.bind] at h ⊢
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp [VEq]
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; simp [VEq, ew]
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

theorem encodeArm_vals {tr : Tier} {as : List Ty} {j : Nat} {p p' q : List Word}
    (e : VEq p p') (h : encodeArm tr as j p = some q) :
    ∃ q', encodeArm tr as j p' = some q' ∧ VEq q q' := by
  cases tr with
  | boxed => simp [encodeArm] at h
  | wide =>
      match p, e, h with
      | [], e, h =>
          have : p' = [] := by cases p' <;> simp_all [VEq]
          subst this; exact ⟨q, h, rfl⟩
      | [w], e, h =>
          obtain ⟨w', rfl, ew⟩ := veq_one e
          simp [encodeArm] at h ⊢; subst h; simp [VEq, ew]
      | _ :: _ :: _, _, h => simp [encodeArm] at h
  | niche =>
      simp only [encodeArm, bind, Option.bind] at h ⊢
      cases h1 : as[j]? with
      | none => simp [h1] at h
      | some a =>
          simp only [h1] at h ⊢
          match p, e, h with
          | [], e, h =>
              have : p' = [] := by cases p' <;> simp_all [VEq]
              subst this; exact ⟨q, h, rfl⟩
          | [w], e, h =>
              obtain ⟨w', rfl, ew⟩ := veq_one e
              cases hk : armK a with
              | ptr =>
                  simp only [hk] at h ⊢; rw [ew]
                  cases hw : w.val <;> simp only [hw] at h <;> simp at h
                  subst h; simp [VEq]
              | opt =>
                  simp only [hk] at h ⊢; rw [ew]
                  cases hw : w.val <;> simp only [hw] at h <;> simp at h
                  · subst h; simp [VEq]
                  · subst h; simp [VEq]
              | nil => simp [hk] at h
              | wide => simp [hk] at h
          | _ :: _ :: _, _, h =>
              cases hk : armK a <;> simp [hk] at h

theorem ofArm_vals {t : Ty} {j : Nat} {p p' q : List Word} (e : VEq p p') (h : ofArm t j p = some q) :
    ∃ q', ofArm t j p' = some q' ∧ VEq q q' := by
  unfold ofArm at h ⊢
  split at h
  · rename_i hs; rw [if_pos hs]; exact encodeArm_vals e h
  · rename_i hs; rw [if_neg hs]
    split at h
    · simp at h; subst h; exact ⟨p', by simp_all, e⟩
    · simp at h

theorem asArm_vals {t : Ty} {ws ws' : List Word} {j : Nat} {p : List Word} (e : VEq ws ws')
    (h : asArm t ws = some (j, p)) : ∃ p', asArm t ws' = some (j, p') ∧ VEq p p' := by
  unfold asArm at h ⊢
  split at h
  · rename_i hs; rw [if_pos hs]; exact decodeArm_vals e h
  · rename_i hs; rw [if_neg hs]; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨ws', by simp, e⟩

inductive Shp
  | leaf (n : Option Nat)
  | prod (a b : Shp)
  | iex (n : Option Nat) (b : Shp)
  | fix (sg : Bool) (w : Wd)
  | lanes (sg : Bool) (w : Wd)
  | sum (n : Option Nat) (R : Ty)   -- a runtime sum, in layout normal form
  | code (A B : Ty)   -- a code value's runtime signature, as `sig`s
  | tex (n : Option Nat) (b : Shp)   -- a type-existential package (24e)

def Shp.wc : Shp → Option Nat
  | .leaf n => n
  | .prod a b => do pure ((← a.wc) + (← b.wc))
  | .iex n _ => n
  | .fix _ _ => some 1
  | .lanes _ _ => some 1
  | .sum n _ => n
  | .code _ _ => some 1
  | .tex n _ => n

def shp : Ty → Shp
  | .prod a b => .prod (shp a) (shp b)
  | .iex b => .iex (wc (.iex b)) (shp b)
  | .fix sg w => .fix sg w
  | .lanes sg w => .lanes sg w
  | .refine t _ => shp t   -- `VR` at `{t | ψ}` is `VR` at `t`, on the same words
  | .mu t => shp t         -- likewise `μ` (T3c-5a): its layout is its body's (`accs`)
  | .iall t => shp t       -- likewise `∀` (T3c-5f): indices are erased
  | .sum a b => .sum (wc (.sum a b)) (lnorm (.sum a b))
  | .code _ _ => .code .unit .unit
  | .tex κ b => .tex (wc (.tex κ b)) (shp b)
  | t => .leaf (wc t)

theorem wc_some {t : Ty} {n : Nat} (h : wc t = some n) : ∃ us, accs t = some us ∧ nWords us = n := by
  unfold wc at h
  cases hu : accs t with
  | none => simp [hu] at h
  | some us => simp only [hu, Option.map_some, Option.some.injEq] at h; exact ⟨us, rfl, h⟩

/-- A shape's word count is its runtime type's. -/
theorem shp_wc : ∀ t : Ty, (shp t).wc = wc t := by
  intro t
  induction t with
  | prod a b iha ihb =>
      simp only [shp, Shp.wc, iha, ihb, wc]
      cases ha : accs a <;> cases hb : accs b <;> simp [accs, ha, hb, nWords]
  | iex b _ => rfl
  | fix _ _ => simp [shp, Shp.wc, wc, accs, nWords, Acc.size]
  | lanes _ _ => simp [shp, Shp.wc, wc, accs, nWords, Acc.size]
  | refine t _ ih => simp only [shp, ih, wc, accs]
  | mu t ih => simp only [shp, ih, wc, accs]
  | iall t ih => simp only [shp, ih, wc, accs]
  | _ => rfl

/-- Two runtime renditions of a value that the value relation cannot tell apart. -/
def Agree (r r' : Ty) : Prop := shp r = shp r'

theorem Agree.refl (r : Ty) : Agree r r := rfl
theorem Agree.symm {r r' : Ty} (h : Agree r r') : Agree r' r := Eq.symm h
theorem Agree.trans {r r' r'' : Ty} (h : Agree r r') (h' : Agree r' r'') : Agree r r'' :=
  Eq.trans h h'

/-- Agreeing runtime types have layouts of the same word count. -/
theorem Agree.wc {r r' : Ty} (h : Agree r r') : wc r = wc r' := by
  rw [← shp_wc, ← shp_wc, h]

/-! ## §2 The value relation -/

/-- **A cell of the store typing Σ** (T3c-3).  Σ is syntactic
(option B): a cell records the closed type of its contents; what the contents
mean is `VR` at that type.  `owner`: `some i` for thread `i`'s own cell, `none`
once published. -/
structure Cell where
  ty : Ty
  owner : Option Nat

/-- (T3c-5a) What a locative may target has a layout: a value (`accs`), or a
buffer of laid-out slots.  `fld` and `idx` read the skipped components' widths. -/
def LayT (t : Ty) : Prop := accs t ≠ none ∨ ∃ n e, t = .array (.lit n) e ∧ accs e ≠ none

/-- `AtOff T o U`: word offset `o` of a value of the closed type `T` starts a
component of type `U` (the target of a locative), which has a layout (`LayT`).
Pairs, arrays of literal length, and (T3c-5a) `μ` types, through their
unfolding.  The `μ` case is stated on closures, `cl ρ W 0 0 (μ s)`, so `fld`
needs no commutation of closing with unfolding. -/
inductive AtOff : Ty → Nat → Ty → Prop
  | here {t : Ty} : LayT t → AtOff t 0 t
  | fst {a b u : Ty} {o : Nat} : AtOff a o u → AtOff (.prod a b) o u
  | snd {a b u : Ty} {o : Nat} {us : List Acc} : accs a = some us → AtOff b o u →
      AtOff (.prod a b) (nWords us + o) u
  | elem {e u : Ty} {n j o : Nat} {us : List Acc} : accs e = some us → j < n → AtOff e o u →
      AtOff (.array (.lit n) e) (j * nWords us + o) u
  | mu {ρ : Nat → Nat} {W : Nat → Ty} {s u : Ty} {o : Nat} : (∀ k, Clo (W k)) → s.unguarded 0 = false →
      AtOff (cl ρ W 0 0 (unfold1 (.mu s))) o u → AtOff (cl ρ W 0 0 (.mu s)) o u
  | fold {ρ : Nat → Nat} {W : Nat → Ty} {s T : Ty} {o : Nat} : (∀ k, Clo (W k)) → s.unguarded 0 = false →
      accs (cl ρ W 0 0 (.mu s)) ≠ none →
      AtOff T o (cl ρ W 0 0 (unfold1 (.mu s))) → AtOff T o (cl ρ W 0 0 (.mu s))

/-- (T3c-5h) `Fd T U`: a value of the closed type `T` is one of `U`, which folds
some `μ`s back over their unfoldings (`fold`, the op).  A reference's cell holds
the type its pointee type folds (`VR` at `ptr`). -/
inductive Fd : Ty → Ty → Prop
  | refl {t : Ty} : Fd t t
  | fold {ρ : Nat → Nat} {W : Nat → Ty} {s T : Ty} : (∀ k, Clo (W k)) → s.unguarded 0 = false →
      accs (cl ρ W 0 0 (unfold1 (.mu s))) = accs (cl ρ W 0 0 (.mu s)) →
      Fd T (cl ρ W 0 0 (unfold1 (.mu s))) → Fd T (cl ρ W 0 0 (.mu s))

/-- What a reference's mode says about its cell: `own` — this thread's (`tid`);
`pub` — (T3c-5c) published, at frontier `f` (`P`), and the reference's word
carries a view past `f` or the thread has seen the cell (`S`), so a dependent
load through it reads no allocation placeholder (Σ-locality); `rgn r` — T3d
(regions and capabilities), unconstrained. -/
def ModeOK (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    Mode → WeakMem.AllocLabel → Cell → List Word → Prop
  | .own, _, c, _ => c.owner = some i
  | .pub, l, _, ws => ∃ f, P l = some f ∧ (S l ∨ ∀ w ∈ ws, f ≤ w.view)
  | .rgn _, _, _, _ => True

theorem ModeOK_shift (i c : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop)
    (μ : Mode) : ModeOK i P S (μ.shift c) = ModeOK i P S μ := by cases μ <;> rfl
theorem ModeOK_inst (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop)
    (us : List Idx) (d : Nat) (μ : Mode) : ModeOK i P S (instM us d μ) = ModeOK i P S μ := by
  cases μ <;> rfl
theorem ModeOK_clM (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop)
    (ρ : Nat → Nat) (d : Nat) (μ : Mode) : ModeOK i P S (clM ρ d μ) = ModeOK i P S μ := by
  cases μ <;> rfl
theorem ModeOK_meq {i : Nat} {P : WeakMem.AllocLabel → Option WeakMem.Ts} {S : WeakMem.AllocLabel → Prop}
    {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEq cx d μ ν) : ModeOK i P S μ = ModeOK i P S ν := by
  cases h <;> rfl

/-- `ModeOK` survives a larger frontier map, a larger seen set, and larger
views of pointer words. -/
theorem ModeOK_mono {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws ws' : List Word}
    (hw : ∀ f, (∀ w ∈ ws, f ≤ w.view) → ∀ w ∈ ws', f ≤ w.view) :
    ModeOK i P S μ l c ws → ModeOK i P' S' μ l c ws' := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2⟩
    · exact ⟨f, hP l f h1, Or.inl (hS l h2)⟩
    · exact ⟨f, hP l f h1, Or.inr (hw f h2)⟩
  | rgn _ => exact id

/-- (T3c-5d) **A boxed sum's block** (§3.5 tier 3), as a ghost: born frozen, so
its words are fixed at the injection.  `tag`: the flattened arm of the sum it
was built at; `pay`: the payload words as written; `own`: the thread that
built it; `fr`: that thread's `vWr` after the `dmb ishst` (a reader whose
bound reaches it reads no allocation placeholder, T3c-6).  Box labels are
never Σ cells, so no reference writes them. -/
structure Box where
  tag : Nat
  pay : List Word
  own : Nat
  fr : WeakMem.Ts

/-! ### (T3d-2 A1) Resources

A value's **resources** ("Decision and plan: A1"): how many of
each kind of token it carries, counted exactly.  `rg n`: a region token of
region `n` (`tok`, `tok2`); `ep n j`: the epoch-`j` token of region `n`
(`tokE`); `sh n`: a read share of region `n` (`share`).  Counts add over the
parts of a value.  Exclusivity (at most one `rg n` in the whole
configuration) is stages B and C; A1 only makes the counts exact. -/

inductive Key
  | rg (n : Nat)
  | ep (n j : Nat)
  | sh (n : Nat)
  /-- (W1) The word of region `n`: carried by a
  fresh token `tok r none` and by every word or pair value of the region,
  held or not.  At most one per region in a configuration. -/
  | wd (n : Nat)
  /-- (F2′ amendment A) The own handle of
  allocation `l`: minted at the allocation, carried by every non-null `own`
  reference to `l`, dropped by `publish`/`intoRgn`/`region`/`regionBuf`.  At
  most one per label in a configuration. -/
  | own (l : Nat)
  deriving DecidableEq, Repr

/-- A multiset of keys. -/
def Res : Type := Key → Nat

namespace Res

def zero : Res := fun _ => 0

def add (a b : Res) : Res := fun k => a k + b k

instance : Add Res := ⟨Res.add⟩

/-- One token of key `k`. -/
def one (k : Key) : Res := fun k' => if k' = k then 1 else 0

def sum : List Res → Res
  | [] => zero
  | r :: rs => r + sum rs

@[simp] theorem zero_apply (k : Key) : zero k = 0 := rfl
@[simp] theorem add_apply (a b : Res) (k : Key) : (a + b) k = a k + b k := rfl
@[simp] theorem one_apply (k k' : Key) : one k k' = if k' = k then 1 else 0 := rfl
@[simp] theorem sum_nil : sum [] = zero := rfl
@[simp] theorem sum_cons (r : Res) (rs : List Res) : sum (r :: rs) = r + sum rs := rfl

theorem ext {a b : Res} (h : ∀ k, a k = b k) : a = b := funext h

theorem add_comm (a b : Res) : a + b = b + a := ext fun k => Nat.add_comm _ _
theorem add_assoc (a b c : Res) : a + b + c = a + (b + c) := ext fun k => Nat.add_assoc _ _ _
@[simp] theorem zero_add (a : Res) : zero + a = a := ext fun k => Nat.zero_add _
@[simp] theorem add_zero (a : Res) : a + zero = a := ext fun k => Nat.add_zero _

theorem sum_append (xs ys : List Res) : sum (xs ++ ys) = sum xs + sum ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, sum_cons, ih, add_assoc]

theorem add_eq_zero {a b : Res} (h : a + b = zero) : a = zero ∧ b = zero := by
  constructor <;> refine ext fun k => ?_ <;> have := congrFun h k <;> simp at this <;> simp [this]

theorem one_ne_zero (k : Key) : one k ≠ zero := by
  intro h; have := congrFun h k; simp at this

/-- Pointwise order: `a ≤ b` when `b` holds at least `a`'s keys. -/
def le (a b : Res) : Prop := ∀ k, a k ≤ b k

instance : LE Res := ⟨Res.le⟩

theorem le_def {a b : Res} : a ≤ b ↔ ∀ k, a k ≤ b k := Iff.rfl
theorem le_refl (a : Res) : a ≤ a := fun _ => Nat.le_refl _
theorem le_trans {a b c : Res} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := fun k => Nat.le_trans (h1 k) (h2 k)
theorem add_le_add {a b c d : Res} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  fun k => by simp only [add_apply]; exact Nat.add_le_add (h1 k) (h2 k)
theorem le_add_right (a b : Res) : a ≤ a + b := fun k => by simp
theorem zero_le (a : Res) : zero ≤ a := fun k => by simp

end Res

/-- What each type variable denotes: a relation on (runtime shape, words), and a
closed witness type (T3c, option B); the store typing
and the thread (T3c-3). -/
structure TEnv where
  rels : Nat → Shp → List Word → Prop := fun _ _ _ => False
  /-- (T3c-5d) What each variable denotes in memory, i.e. read with no `seen`
  labels (`TEnv.unsee`): `VR` of a box's payload, a memory value, reads it.
  Coherent views keep it at the witness's values in `CE η.unsee` (`Coh`). -/
  urels : Nat → Shp → List Word → Prop := fun _ _ _ => False
  /-- Each variable's closed witness: what `cl` puts in its place.  A code value
  compares closures of signatures with its block's. -/
  wit : Nat → Ty := fun _ => .void
  /-- The program: a code value is a position in it. -/
  prog : Prog := []
  /-- The store typing Σ (T3c-3): a reference's target cell, by label. -/
  sto : WeakMem.AllocLabel → Option Cell := fun _ => none
  /-- The running thread: whose `own` cells these are. -/
  tid : Nat := 0
  /-- (T3c-5b) Ghost: how many slots of the buffer at each label are
  initialised. It only grows (`Ext`). -/
  ini : WeakMem.AllocLabel → Nat := fun _ => 0
  /-- (F2′ (a′)) Ghost: the **real** number of
  initialised slots, read only by `own`-mode typing (`TEnv.selIni`, through
  `min ini rini`); `ini` is the reader-visible count (at a planted buffer, the
  predicted one).  It only grows (`Ext`). -/
  rini : WeakMem.AllocLabel → Nat := fun _ => 0
  /-- (T3c-5c) Ghost: each published cell's frontier, the publisher's `vWr` at
  its `dmb ishst`: every allocation placeholder of the cell is hidden from a
  reader whose bound reaches it. It only grows (`Ext`). -/
  pfr : WeakMem.AllocLabel → Option WeakMem.Ts := fun _ => none
  /-- (T3c-5c) Ghost, the thread's: published cells it reads past the
  placeholders of by coherence alone, and whose frontier its plain stores
  carry (the publisher). It only grows (`Ext`). -/
  seen : WeakMem.AllocLabel → Prop := fun _ => False
  /-- (T3c-5d) Ghost: the boxed-sum blocks, by label. It only grows (`Ext`). -/
  box : WeakMem.AllocLabel → Option Box := fun _ => none
  /-- (T3d-2 A0) Ghost: the thread's region counter.  `region` and `openPub`
  name their region `ridPair tid rid` (TermStep) and bump it, so region ids
  are fresh across threads with no cross-thread argument.  It
  only grows (`Ext`).  Not part of `CE`: nothing in memory reads it, so the
  memory invariant is untouched by a bump. -/
  rid : Nat := 0
  /-- (T3d-2 A1) The resourceful `rels`: what each variable denotes, with the
  resources of the value (`VRR`).  Migrating: `rels` goes once `VRR` is `VR`. -/
  rrs : Nat → Shp → List Word → Res → Prop := fun _ _ _ _ => False
  /-- (T3d-2 A1) The resourceful `urels`. -/
  urrs : Nat → Shp → List Word → Res → Prop := fun _ _ _ _ => False
  /-- Ghost: the other threads'
  outstanding promises.  Memory's reading skips them at the non-word units of
  shared cells (`PromAt`); `[]` for a thread alone (stage A builds it so). -/
  fp : List WeakMem.Ts := []

def TEnv.get (η : TEnv) (k : Nat) : Shp → List Word → Prop := η.rels k

/-- `η` with a variable inserted at `c`, denoting `R` (in memory, `UR`), with
witness `s`. -/
def TEnv.insR (c : Nat) (R : Shp → List Word → Prop) (s : Ty) (η : TEnv)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) : TEnv :=
  { η with
    rels := fun k => if k < c then η.rels k else if k = c then R else η.rels (k - 1),
    urels := fun k => if k < c then η.urels k else if k = c then UR else η.urels (k - 1),
    rrs := fun k => if k < c then η.rrs k else if k = c then RR else η.rrs (k - 1),
    urrs := fun k => if k < c then η.urrs k else if k = c then URR else η.urrs (k - 1),
    wit := fun k => if k < c then η.wit k else if k = c then s else η.wit (k - 1) }

/-- A variable with witness `s` and no values: a package's witness inside `VR`.
The term layer's `guardT` keeps it where `VR` reads only witnesses. -/
def TEnv.ins (c : Nat) (s : Ty) (η : TEnv) : TEnv := η.insR c (fun _ _ => False) s

/-- Under a type binder (`∃α`): the new variable is 0. -/
def TEnv.push0 (η : TEnv) (s : Ty) : TEnv := η.ins 0 s

/-- Several type binders, witnesses `P` (`P[0]` innermost). -/
def TEnv.pre : List Ty → TEnv → TEnv
  | [], η => η
  | s :: P, η => (TEnv.pre P η).push0 s

theorem TEnv.insR_prog (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).prog = η.prog := rfl
theorem TEnv.insR_sto (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).sto = η.sto := rfl
theorem TEnv.insR_tid (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).tid = η.tid := rfl
theorem TEnv.insR_ini (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).ini = η.ini := rfl
theorem TEnv.insR_rini (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).rini = η.rini := rfl
theorem TEnv.insR_pfr (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).pfr = η.pfr := rfl
theorem TEnv.insR_seen (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).seen = η.seen := rfl
theorem TEnv.insR_box (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).box = η.box := rfl

theorem push0_rels_zero (η : TEnv) (s : Ty) : (η.push0 s).rels 0 = fun _ _ => False := by
  simp [TEnv.push0, TEnv.ins, TEnv.insR]
theorem push0_rels_succ (η : TEnv) (s : Ty) (k : Nat) : (η.push0 s).rels (k + 1) = η.rels k := by
  simp [TEnv.push0, TEnv.ins, TEnv.insR]
theorem push0_urels_zero (η : TEnv) (s : Ty) : (η.push0 s).urels 0 = fun _ _ => False := by
  simp [TEnv.push0, TEnv.ins, TEnv.insR]
theorem push0_urels_succ (η : TEnv) (s : Ty) (k : Nat) : (η.push0 s).urels (k + 1) = η.urels k := by
  simp [TEnv.push0, TEnv.ins, TEnv.insR]

theorem push0_rels_mono {η₁ η₂ : TEnv} {s s' : Ty} (hr : ∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) :
    ∀ k S vs, (η₁.push0 s).rels k S vs → (η₂.push0 s').rels k S vs
  | 0, _, _, h => by rw [push0_rels_zero] at h; exact h.elim
  | k + 1, S, vs, h => by rw [push0_rels_succ] at h ⊢; exact hr k S vs h
theorem push0_urels_mono {η₁ η₂ : TEnv} {s s' : Ty} (hr : ∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) :
    ∀ k S vs, (η₁.push0 s).urels k S vs → (η₂.push0 s').urels k S vs
  | 0, _, _, h => by rw [push0_urels_zero] at h; exact h.elim
  | k + 1, S, vs, h => by rw [push0_urels_succ] at h ⊢; exact hr k S vs h

/-- A code value's own view: no type variables (witnesses `void`); the
program, the store typing and the thread are the caller's. -/
def CE (η : TEnv) : TEnv :=
  { prog := η.prog, sto := η.sto, tid := η.tid, ini := η.ini, rini := η.rini, pfr := η.pfr, seen := η.seen,
    box := η.box, fp := η.fp }

theorem CE_prog (η : TEnv) : (CE η).prog = η.prog := rfl
theorem CE_sto (η : TEnv) : (CE η).sto = η.sto := rfl
theorem CE_tid (η : TEnv) : (CE η).tid = η.tid := rfl
theorem CE_ini (η : TEnv) : (CE η).ini = η.ini := rfl
theorem CE_rini (η : TEnv) : (CE η).rini = η.rini := rfl
theorem CE_pfr (η : TEnv) : (CE η).pfr = η.pfr := rfl
theorem CE_seen (η : TEnv) : (CE η).seen = η.seen := rfl
theorem CE_box (η : TEnv) : (CE η).box = η.box := rfl
theorem CE_fp (η : TEnv) : (CE η).fp = η.fp := rfl

/-- (T3c-6 prep) The box at `l` is one the thread has seen up to its frontier:
`l` is `seen` with a recorded frontier at least the box's.  Like `ModeOK pub`
for a published cell, a box reference is a value either here or, in memory
(`unsee` drops `seen`), when its word's view reaches the box's frontier; so
`VR` never reads the thread id at a box. -/
def BoxSeen (η : TEnv) (l : WeakMem.AllocLabel) (B : Box) : Prop :=
  η.seen l ∧ ∃ f, η.pfr l = some f ∧ B.fr ≤ f

/-- (D3) The thread's view with no `seen` labels: what a memory value is read
in.  (T3c-5d) Its variables denote their memory relations (`urels`). -/
def TEnv.unsee (η : TEnv) : TEnv := { η with seen := fun _ => False, rels := η.urels, rrs := η.urrs }

theorem unsee_insR (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop) (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.insR c R s UR RR URR).unsee = η.unsee.insR c UR s UR URR URR := rfl

theorem unsee_push0 (η : TEnv) (s : Ty) : (η.push0 s).unsee = η.unsee.push0 s := rfl

theorem unsee_pre (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).unsee = TEnv.pre P η.unsee
  | [] => rfl
  | s :: P => by rw [TEnv.pre, unsee_push0, unsee_pre η P]; rfl

theorem unsee_unsee (η : TEnv) : η.unsee.unsee = η.unsee := rfl

theorem CE_unsee (η : TEnv) : (CE η).unsee = CE η.unsee := rfl

theorem insR_push0 (η : TEnv) (c : Nat) (R : Shp → List Word → Prop) (s s' : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    (η.push0 s').insR (c + 1) R s UR RR URR = (η.insR c R s UR RR URR).push0 s' := by
  have key : ∀ {α : Type} (f : Nat → α) (x y : α) (j : Nat),
      (if j < c then f j else if j = c then x else if j = 0 then y else f (j - 1)) =
      (if j < c then f j else if j = c then x else f (j - 1)) := by
    intro α f x y j
    by_cases h1 : j < c
    · simp [h1]
    · by_cases h2 : j = c
      · simp [h2]
      · have h3 : j ≠ 0 := by omega
        simp [h1, h2, h3]
  simp only [TEnv.push0, TEnv.ins, TEnv.insR]
  congr 1 <;> funext k <;> rcases k with _ | j <;> simp <;> exact key _ _ _ j

theorem pre_prog (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).prog = η.prog
  | [] => rfl
  | _ :: P => pre_prog η P

theorem pre_sto (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).sto = η.sto
  | [] => rfl
  | _ :: P => pre_sto η P

theorem pre_tid (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).tid = η.tid
  | [] => rfl
  | _ :: P => pre_tid η P

theorem pre_ini (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).ini = η.ini
  | [] => rfl
  | _ :: P => pre_ini η P

theorem pre_rini (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).rini = η.rini
  | [] => rfl
  | _ :: P => pre_rini η P

theorem pre_pfr (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).pfr = η.pfr
  | [] => rfl
  | _ :: P => pre_pfr η P

theorem pre_seen (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).seen = η.seen
  | [] => rfl
  | _ :: P => pre_seen η P

theorem pre_box (η : TEnv) : ∀ P : List Ty, (TEnv.pre P η).box = η.box
  | [] => rfl
  | _ :: P => pre_box η P

theorem pre_rels (η : TEnv) : ∀ (P : List Ty) (k : Nat),
    (TEnv.pre P η).rels k = if k < P.length then (fun _ _ => False) else η.rels (k - P.length)
  | [], k => by simp [TEnv.pre]
  | s :: P, k => by
      have ih := pre_rels η P (k - 1)
      simp only [TEnv.pre, TEnv.push0, TEnv.ins, TEnv.insR, List.length_cons] at ih ⊢
      rcases k with _ | j
      · simp
      · simp only [Nat.add_sub_cancel] at ih
        by_cases h : j < P.length
        · simp [h, ih]
        · simp [h, ih]

theorem pre_rrs (η : TEnv) : ∀ (P : List Ty) (k : Nat),
    (TEnv.pre P η).rrs k = if k < P.length then (fun _ _ _ => False) else η.rrs (k - P.length)
  | [], k => by simp [TEnv.pre]
  | s :: P, k => by
      have ih := pre_rrs η P (k - 1)
      simp only [TEnv.pre, TEnv.push0, TEnv.ins, TEnv.insR, List.length_cons] at ih ⊢
      rcases k with _ | j
      · simp
      · simp only [Nat.add_sub_cancel] at ih
        by_cases h : j < P.length
        · simp [h, ih]
        · simp [h, ih]

theorem pre_get (η : TEnv) (P : List Ty) (k : Nat) :
    (TEnv.pre P η).get k = if k < P.length then (fun _ _ => False) else η.get (k - P.length) := by
  simp only [TEnv.get, pre_rels]

theorem pre_wit_lt (X Y : TEnv) : ∀ (P : List Ty) (k : Nat), k < P.length →
    (TEnv.pre P X).wit k = (TEnv.pre P Y).wit k
  | [], k, h => absurd h (Nat.not_lt_zero _)
  | s :: P, k, h => by
      rcases k with _ | j
      · simp [TEnv.pre, TEnv.push0, TEnv.ins, TEnv.insR]
      · have := pre_wit_lt X Y P j (by simp at h; omega)
        simp [TEnv.pre, TEnv.push0, TEnv.ins, TEnv.insR, this]

theorem pre_wit_ge (η : TEnv) : ∀ (P : List Ty) (k : Nat), P.length ≤ k →
    (TEnv.pre P η).wit k = η.wit (k - P.length)
  | [], k, _ => rfl
  | s :: P, k, h => by
      rcases k with _ | j
      · simp at h
      · have := pre_wit_ge η P j (by simp at h; omega)
        simp [TEnv.pre, TEnv.push0, TEnv.ins, TEnv.insR, this]

/-- A declared (closed) type's closure: what a code value's signature is
compared with. -/
def clD (A : Ty) : Ty := cl (fun _ => 0) (fun _ => .void) 0 0 A

theorem cl_vins (c w : Nat) (ρ : Nat → Nat) (W : Nat → Ty) (t : Ty) :
    cl (vins c w ρ) W 0 0 (t.shiftI c) = cl ρ W 0 0 t := by
  have h : ∀ k, vins c w ρ (if c ≤ k then k + 1 else k) = ρ k := by
    intro k
    by_cases hk : c ≤ k
    · have h1 : ¬ k + 1 < c := by omega
      have h2 : k + 1 ≠ c := by omega
      simp [vins, hk, h1, h2]
    · have h1 : k < c := by omega
      simp [vins, hk, h1]
  exact cl_shiftI h W t 0 0

theorem cl_insR (c : Nat) (R : Shp → List Word → Prop) (s : Ty) (η : TEnv) (ρ : Nat → Nat) (t : Ty)
    (UR : Shp → List Word → Prop := fun _ _ => False)
    (RR : Shp → List Word → Res → Prop := fun _ _ _ => False)
    (URR : Shp → List Word → Res → Prop := fun _ _ _ => False) :
    cl ρ (η.insR c R s UR RR URR).wit 0 0 (t.shiftT c) = cl ρ η.wit 0 0 t := by
  have h : ∀ k, (η.insR c R s UR RR URR).wit (if c ≤ k then k + 1 else k) = η.wit k := by
    intro k
    by_cases hk : c ≤ k
    · have h1 : ¬ k + 1 < c := by omega
      have h2 : k + 1 ≠ c := by omega
      simp [TEnv.insR, hk, h1, h2]
    · have h1 : k < c := by omega
      simp [TEnv.insR, hk, h1]
  exact cl_shiftT h ρ t 0 0

theorem cl_inst1 (w : Idx) (d : Nat) (ρ : Nat → Nat) (W : Nat → Ty) (t : Ty) :
    cl ρ W 0 0 (instT [w] d t) = cl (vins d (ev (fun k => ρ (k + d)) w) ρ) W 0 0 t :=
  cl_instT (us := [w]) (d0 := d) (ρ := ρ) (ρ' := vins d (ev (fun k => ρ (k + d)) w) ρ)
    (fun k hk => by simp [vins, hk])
    (fun j u hj => by
      cases j with
      | zero => simp at hj; subst hj; simp [vins]
      | succ j => simp at hj)
    (fun k => by
      have h1 : ¬ d + [w].length + k < d := by simp; omega
      have h2 : d + [w].length + k ≠ d := by simp; omega
      simp only [vins, h1, h2, if_false]
      congr 1; simp <;> omega) W t 0 0

/-- (T3c-5b) What a buffer handle's `ini k` says: `k` slots of the buffer it
points at are initialised (`ini`, the ghost count `TEnv.ini`). -/
def IniR (ρ : Nat → Nat) (ini : WeakMem.AllocLabel → Nat) : Pred → List Word → Prop
  | .ini k, ws => ∀ a : WeakMem.Address, ws.map (·.val) = [.loc a 0] → ev ρ k ≤ ini a.label
  | .and p q, ws => IniR ρ ini p ws ∧ IniR ρ ini q ws
  | _, _ => True

/-- (T3c-5b) A locative into a buffer (a cell `array (lit N) e`) targets the whole
buffer, or a component of an initialised slot `j`. -/
def IniAt (ini : WeakMem.AllocLabel → Nat) (c : Cell) (a : WeakMem.Address) (U : Ty) : Prop :=
  ∀ N e, c.ty = .array (.lit N) e → (U = c.ty ∧ 0 = a.offset) ∨
    ∃ us j o, accs e = some us ∧ j < ini a.label ∧ j * nWords us + o = a.offset ∧ AtOff e o U

theorem IniAt_mono {i₁ i₂ : WeakMem.AllocLabel → Nat} (h : ∀ l, i₁ l ≤ i₂ l) {c : Cell} {a : WeakMem.Address}
    {U : Ty} (hv : IniAt i₁ c a U) : IniAt i₂ c a U := by
  intro N e hc
  rcases hv N e hc with h1 | ⟨us, j, o, h1, h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr ⟨us, j, o, h1, Nat.lt_of_lt_of_le h2 (h _), h3, h4⟩

/-- Not a buffer: nothing to say. -/
theorem IniAt_of_ne {ini : WeakMem.AllocLabel → Nat} {c : Cell} {a : WeakMem.Address} {U : Ty}
    (h : ∀ N e, c.ty ≠ .array (.lit N) e) : IniAt ini c a U :=
  fun N e hc => absurd hc (h N e)

theorem IniR_vals {ρ : Nat → Nat} {ini : WeakMem.AllocLabel → Nat} {ws ws' : List Word}
    (e : ws.map (·.val) = ws'.map (·.val)) : ∀ ψ : Pred, IniR ρ ini ψ ws → IniR ρ ini ψ ws' := by
  intro ψ
  induction ψ with
  | ini k => intro h; simp only [IniR] at h ⊢; intro a ha; exact h a (e.trans ha)
  | and p q ihp ihq => intro h; simp only [IniR] at h ⊢; exact ⟨ihp h.1, ihq h.2⟩
  | _ => intro _; simp [IniR]

theorem IniR_mono {ρ : Nat → Nat} {i₁ i₂ : WeakMem.AllocLabel → Nat} (h : ∀ l, i₁ l ≤ i₂ l)
    {ws : List Word} : ∀ {ψ : Pred}, IniR ρ i₁ ψ ws → IniR ρ i₂ ψ ws := by
  intro ψ
  induction ψ with
  | ini k => intro hv; simp only [IniR] at hv ⊢; intro a ha; exact Nat.le_trans (hv a ha) (h _)
  | and p q ihp ihq => intro hv; simp only [IniR] at hv ⊢; exact ⟨ihp hv.1, ihq hv.2⟩
  | _ => intro _; simp [IniR]

theorem IniR_shift (c w : Nat) (ρ : Nat → Nat) (ini : WeakMem.AllocLabel → Nat) (ws : List Word) :
    ∀ ψ : Pred, IniR (vins c w ρ) ini (ψ.shift c) ws ↔ IniR ρ ini ψ ws := by
  intro ψ
  induction ψ with
  | ini k => simp only [Pred.shift, IniR, ev_shift]
  | and p q ihp ihq => simp only [Pred.shift, IniR, ihp, ihq]
  | _ => simp [Pred.shift, IniR]

theorem IniR_inst (w : Idx) (d : Nat) (ρ : Nat → Nat) (ini : WeakMem.AllocLabel → Nat) (ws : List Word) :
    ∀ ψ : Pred, IniR ρ ini (instP [w] d ψ) ws ↔ IniR (vins d (ev (fun k => ρ (k + d)) w) ρ) ini ψ ws := by
  intro ψ
  induction ψ with
  | ini k => simp only [instP, IniR, ev_instI]
  | and p q ihp ihq => simp only [instP, IniR, ihp, ihq]
  | _ => simp [instP, IniR]

theorem IniR_cl {ρ ρ₀ ρ' : Nat → Nat} {d : Nat} (hρ : ∀ k, ρ (k + d) = ρ₀ k)
    (hρ' : ∀ k, k < d → ρ' k = ρ k) (ini : WeakMem.AllocLabel → Nat) (ws : List Word) :
    ∀ ψ : Pred, IniR ρ ini ψ ws ↔ IniR ρ' ini (clP ρ₀ d ψ) ws := by
  intro ψ
  induction ψ with
  | ini k => simp only [clP, IniR, ev_clI hρ hρ']
  | and p q ihp ihq => simp only [clP, IniR, ihp, ihq]
  | _ => simp [clP, IniR]

/-- (F2′ (a′)) An `own` reference at the head. -/
def _root_.CoreLang.Ty.ownHead : Ty → Bool
  | .loc .own _ | .ptr .own _ | .ptrOpt .own _ => true
  | _ => false

/-- (F2′ (a′)) The refined type is an `own` reference, reading a type variable
through its witness (so the choice is stable under closing and substitution). -/
def TEnv.ownTop (η : TEnv) : Ty → Bool
  | .tvar k => (η.wit k).ownHead
  | t => t.ownHead

/-- (F2′ (a′)) **The count an `ini` refinement of `t` reads**: an `own`
reference reads the real count (`min ini rini`, so that it also bounds `ini`
and converts to a `pub` one at `publish`); every other one reads the
reader-visible `ini`. -/
def TEnv.selIni (η : TEnv) (t : Ty) : WeakMem.AllocLabel → Nat :=
  if η.ownTop t then fun l => min (η.ini l) (η.rini l) else η.ini

theorem TEnv.selIni_le_ini (η : TEnv) (t : Ty) (l : WeakMem.AllocLabel) : η.selIni t l ≤ η.ini l := by
  unfold TEnv.selIni; split
  · exact Nat.min_le_left _ _
  · exact Nat.le_refl _

theorem TEnv.ownTop_congr {η₁ η₂ : TEnv} (hw : η₁.wit = η₂.wit) (t : Ty) : η₁.ownTop t = η₂.ownTop t := by
  cases t <;> simp [TEnv.ownTop, hw]

theorem TEnv.selIni_le {η₁ η₂ : TEnv} (hw : η₁.wit = η₂.wit) (hi : ∀ l, η₁.ini l ≤ η₂.ini l)
    (hri : ∀ l, η₁.rini l ≤ η₂.rini l) (t : Ty) : ∀ l, η₁.selIni t l ≤ η₂.selIni t l := by
  intro l
  have h1 := hi l; have h2 := hri l
  unfold TEnv.selIni; rw [TEnv.ownTop_congr hw t]; split
  · simp only; omega
  · exact h1

/-- `selIni` reads only `wit`, `ini`, `rini`. -/
theorem TEnv.selIni_eq {η₁ η₂ : TEnv} (hw : η₁.wit = η₂.wit) (hi : η₁.ini = η₂.ini)
    (hri : η₁.rini = η₂.rini) (t : Ty) : η₁.selIni t = η₂.selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_congr hw t, hi, hri]

/-- (F2′ (a′)) **The count a locative of mode `μ` reads** (`IniAt`): an `own`
locative reads the real count `min ini rini`, every other one the
reader-visible `ini` (as `selIni` for refinements). -/
def modeIni : Mode → (WeakMem.AllocLabel → Nat) → (WeakMem.AllocLabel → Nat) → WeakMem.AllocLabel → Nat
  | .own, ini, rini => fun l => min (ini l) (rini l)
  | _, ini, _ => ini

theorem modeIni_le_ini (μ : Mode) (ini rini : WeakMem.AllocLabel → Nat) (l : WeakMem.AllocLabel) :
    modeIni μ ini rini l ≤ ini l := by
  cases μ <;> simp only [modeIni] <;> omega

theorem modeIni_le {i₁ i₂ r₁ r₂ : WeakMem.AllocLabel → Nat} (hi : ∀ l, i₁ l ≤ i₂ l)
    (hri : ∀ l, r₁ l ≤ r₂ l) (μ : Mode) : ∀ l, modeIni μ i₁ r₁ l ≤ modeIni μ i₂ r₂ l := by
  intro l
  have h1 := hi l; have h2 := hri l
  cases μ <;> simp only [modeIni] <;> omega

theorem modeIni_shift (c : Nat) (μ : Mode) : modeIni (μ.shift c) = modeIni μ := by
  cases μ <;> rfl
theorem modeIni_inst (us : List Idx) (d : Nat) (μ : Mode) : modeIni (instM us d μ) = modeIni μ := by
  cases μ <;> rfl
theorem modeIni_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) : modeIni (clM ρ d μ) = modeIni μ := by
  cases μ <;> rfl
theorem modeIni_meq {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEq cx d μ ν) : modeIni μ = modeIni ν := by
  cases h <;> rfl

/-- A refinement of a locative reads the count its mode reads. -/
theorem TEnv.selIni_loc (η : TEnv) (μ : Mode) (t : Ty) : η.selIni (.loc μ t) = modeIni μ η.ini η.rini := by
  cases μ <;> rfl

theorem TEnv.ownTop_shiftI (η : TEnv) (c : Nat) (t : Ty) : η.ownTop (t.shiftI c) = η.ownTop t := by
  cases t with
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.selIni_shiftI (η : TEnv) (c : Nat) (t : Ty) : η.selIni (t.shiftI c) = η.selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_shiftI]

theorem TEnv.ownTop_instT (η : TEnv) (us : List Idx) (d : Nat) (t : Ty) : η.ownTop (instT us d t) = η.ownTop t := by
  cases t with
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.selIni_instT (η : TEnv) (us : List Idx) (d : Nat) (t : Ty) : η.selIni (instT us d t) = η.selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_instT]

theorem TEnv.ownTop_tyEq (η : TEnv) {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) : η.ownTop t = η.ownTop u := by
  cases h with
  | ptr hm _ => cases hm <;> rfl
  | ptrOpt hm _ => cases hm <;> rfl
  | loc hm _ => cases hm <;> rfl
  | _ => rfl

theorem TEnv.selIni_tyEq (η : TEnv) {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) : η.selIni t = η.selIni u := by
  unfold TEnv.selIni; rw [TEnv.ownTop_tyEq η h]

theorem TEnv.ownTop_of_Clo (η : TEnv) {s : Ty} (h : Clo s) : η.ownTop s = s.ownHead := by
  cases s with
  | tvar k => exact absurd h.1 (by simp [tb])
  | _ => rfl

theorem TEnv.ownTop_shiftT_insR (η : TEnv) (c : Nat) {R : Shp → List Word → Prop} {s : Ty}
    {UR : Shp → List Word → Prop} {RR URR : Shp → List Word → Res → Prop} (t : Ty) :
    (η.insR c R s UR RR URR).ownTop (t.shiftT c) = η.ownTop t := by
  cases t with
  | tvar k =>
      by_cases h : k ≥ c
      · have h1 : ¬ k + 1 < c := by omega
        have h2 : k + 1 ≠ c := by omega
        simp [Ty.shiftT, h, TEnv.ownTop, TEnv.insR, h1, h2]
      · have h1 : k < c := by omega
        simp [Ty.shiftT, h, TEnv.ownTop, TEnv.insR, h1]
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.selIni_shiftT_insR (η : TEnv) (c : Nat) {R : Shp → List Word → Prop} {s : Ty}
    {UR : Shp → List Word → Prop} {RR URR : Shp → List Word → Res → Prop} (t : Ty) :
    (η.insR c R s UR RR URR).selIni (t.shiftT c) = η.selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_shiftT_insR]; rfl

theorem TEnv.ownTop_shiftTN (σ : Ty) : ∀ (P : List Ty) (η : TEnv),
    (TEnv.pre P η).ownTop (shiftTN P.length σ) = η.ownTop σ
  | [], _ => rfl
  | s :: P, η => by
      show ((TEnv.pre P η).insR 0 (fun _ _ => False) s).ownTop (Ty.shiftT 0 (shiftTN P.length σ)) = _
      rw [TEnv.ownTop_shiftT_insR]; exact TEnv.ownTop_shiftTN σ P η

theorem TEnv.ownTop_shiftIN (η : TEnv) (σ : Ty) : ∀ d, η.ownTop (shiftIN d σ) = η.ownTop σ
  | 0 => rfl
  | d + 1 => by
      show η.ownTop (Ty.shiftI 0 (shiftIN d σ)) = _
      rw [TEnv.ownTop_shiftI]; exact TEnv.ownTop_shiftIN η σ d

theorem TEnv.ownHead_cl0 (η : TEnv) (ρ₀ : Nat → Nat) (d : Nat) (σ : Ty) :
    (cl ρ₀ η.wit 0 d σ).ownHead = η.ownTop σ := by
  cases σ with
  | tvar k => simp [cl, TEnv.ownTop]
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.ownTop_cl {η : TEnv} (hw : ∀ k, Clo (η.wit k)) (X : TEnv) (ρ₀ : Nat → Nat) (P : List Ty)
    (d : Nat) (t : Ty) : (TEnv.pre P X).ownTop (cl ρ₀ η.wit P.length d t) = (TEnv.pre P η).ownTop t := by
  cases t with
  | tvar k =>
      by_cases h : k < P.length
      · simp only [cl, h, ↓reduceIte]; exact congrArg Ty.ownHead (pre_wit_lt X η P k h)
      · simp only [cl, h, ↓reduceIte]
        rw [TEnv.ownTop_of_Clo _ (hw _)]
        exact (congrArg Ty.ownHead (pre_wit_ge η P k (by omega))).symm
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.selIni_cl {η : TEnv} (hw : ∀ k, Clo (η.wit k)) (ρ₀ : Nat → Nat) (P : List Ty)
    (d : Nat) (t : Ty) : (TEnv.pre P (CE η)).selIni (cl ρ₀ η.wit P.length d t) = (TEnv.pre P η).selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_cl hw]; simp only [pre_ini, pre_rini, CE_ini, CE_rini]

theorem TEnv.selIni_le_at (η : TEnv) (t : Ty) {a b : WeakMem.AllocLabel} (hi : η.ini a ≤ η.ini b)
    (hri : min (η.ini a) (η.rini a) ≤ η.rini b) : η.selIni t a ≤ η.selIni t b := by
  unfold TEnv.selIni; split
  · simp only; omega
  · exact hi

/-- The autoParam of the `rini` monotonicity hypotheses. -/
macro "rini_le" : tactic =>
  `(tactic| first
    | exact fun _ => Nat.le_refl _
    | assumption
    | exact Ext.rini (by assumption)
    | (intro l; simp))

/-- (S7) No region reference reachable by `VR` (own references allowed; `VR`
does not descend into a reference's target).  Until region cells are covered
(R2), a published cell's type is region-free (TermStep's `PubCpl`, from the
scope), and so is every `share` witness (`WitOK`, `WitR`). -/
def rgnFree : Ty → Bool
  | .ptr (.rgn _) _    => false
  | .ptrOpt (.rgn _) _ => false
  | .loc (.rgn _) _    => false
  | .prod a b      => rgnFree a && rgnFree b
  | .sum a b       => rgnFree a && rgnFree b
  | .array _ t     => rgnFree t
  | .mu t          => rgnFree t
  | .tex _ t       => rgnFree t
  | .iall t        => rgnFree t
  | .iex t         => rgnFree t
  | .refine t _    => rgnFree t
  | _              => true

/-- (T2) Closing keeps `noIallV` when the witnesses have it. -/
theorem noIallV_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, noIallV (W k) = true) (t : Ty) :
    ∀ c d, noIallV t = true → noIallV (cl ρ W c d t) = true := by
  induction t with
  | tvar k =>
      intro c d _
      by_cases h : k < c
      · simp [cl, h, noIallV]
      · simp only [cl, h, ↓reduceIte]; exact hW _
  | tok r i => intro c d _; rcases i with _ | ⟨_, _⟩ <;> simp [cl, noIallV]
  | _ => intro c d h; simp_all [cl, noIallV]

/-- (T3c-5c) What a package's witness carries at runtime: no arrays (as `WitAF`), and, for a
`share` kind, `coupledOK` (what `pack`'s `admitsIn` checked), so that a torn read of a `pub`
cell through the unpacked variable still reads a value (`TermTear`).  (S7) A `share`
witness is region-free (`rgnFree`; the scope's check at `packT`, until R2).  (GStoMg) Its `μ`
bodies are guarded (`mg`, as `WitAF`). -/
def WitOK (κ : Kind) (s : Ty) : Prop := s.arrFree = true ∧ (κ.share = true → Ty.coupledOK s = true) ∧
    (κ.copy = true → Ty.affine s = false) ∧ (κ.noOwn = true → Ty.noOwn s = true) ∧
    (κ.share = true → rgnFree s = true) ∧ noIallV s = true ∧ TermTv.mg s = true

/-- (T3c-5d) A boxed summand read through its enclosing sum's box: the shape of
the summand with the box's tag offset by `s`, the arms to its left, carried in
the (otherwise unread) count of its head sum.  A real value's head sum has
count `wc = 1`, i.e. offset 0 (`vsh_zero`). -/
def vsh (s : Nat) : Shp → Shp
  | .sum _ R => .sum (some (s + 1)) R
  | .iex n b => .iex n (vsh s b)
  | .tex n b => .tex n (vsh s b)
  | r => r

/-! ### (T3c-5d, β1) Runtime validity, ahead of `VR` (whose box clause reads it) -/

/-- The words have the length the runtime type's layout says (when it has one). -/
def ShapeC (rt : Ty) (ws : List Word) : Prop := ∀ us, accs rt = some us → ws.length = nWords us

/-- A payload fits its arm: the arm's closed width, and a pointer arm's word is a
pointer with tag 0 (or null, at a `Ptr?` arm). -/
def PayOK (a : Ty) (p : List Word) : Prop :=
  a.rawWords = some p.length ∧
  (armK a = .ptr → ∃ w adr, p = [w] ∧ w.val = .loc adr 0) ∧
  (armK a = .opt → ∃ w, p = [w] ∧ (w.val = .null ∨ ∃ adr, w.val = .loc adr 0))

/-- The sum case of `Valid`, over the components' own validity. -/
def SumV (Va Vb : List Word → Prop) (a b : Ty) (ws : List Word) : Prop :=
  (Ty.sum a b).tier = .boxed ∨ ∃ j p arm,
    decodeArm (Ty.sum a b).tier (armsOf (.sum a b)) ws = some (j, p) ∧
    (armsOf (.sum a b))[j]? = some arm ∧ PayOK arm p ∧
    (∃ q, encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j p = some q ∧ VEq q ws) ∧
    (j < (armsOf a).length → ∃ q, ofArm a j p = some q ∧ ShapeC a q ∧ wc a ≠ none ∧ Va q) ∧
    ((armsOf a).length ≤ j →
      ∃ q, ofArm b (j - (armsOf a).length) p = some q ∧ ShapeC b q ∧ wc b ≠ none ∧ Vb q)

/-- **Runtime validity** (§3's `Lay`): the words are what the machine's own
matches need at the runtime type — a `Ptr` is a tag-0 pointer, a `Ptr?`/`Loc`
null or one, a pair splits at its left layout, and a non-boxed sum decodes at
the runtime type to a fitting payload, canonically (re-encoding gives the same
values), whose re-encoding into the component is valid there.  `Void` has no
values.  No `η`, no static type: this is what makes the machine's `projM`/`injM`
succeed even where `VR` is still a placeholder (`μ`, `∀`, type variables). -/
def Valid : Ty → List Word → Prop
  | .ptr _ _, ws => ∃ a, ws.map (·.val) = [.loc a 0]
  | .ptrOpt _ _, ws => ws.map (·.val) = [.null] ∨ ∃ a, ws.map (·.val) = [.loc a 0]
  | .loc _ _, ws => ws.map (·.val) = [.null] ∨ ∃ a, ws.map (·.val) = [.loc a 0]
  | .prod a b, ws => ∀ n, wc a = some n → Valid a (ws.take n) ∧ Valid b (ws.drop n)
  | .sum a b, ws => SumV (Valid a) (Valid b) a b ws
  | .void, _ => False
  | .refine t _, ws => Valid t ws
  | .iall t, ws => Valid t ws
  | .iex t, ws => Valid t ws
  | .mu t, ws => Valid t ws
  | .tex _ t, ws => Valid t ws
  | _, _ => True

/-- (T3d-1) `n` is a state of `P`: it lies in some clause's family
`scale·k + off`. -/
def InP (P : Proto) (n : Nat) : Prop :=
  ∃ (c : Nat) (cl : Clause) (k : Nat), P.clauses[c]? = some cl ∧ n = cl.scale * k + cl.off

/-- (T3d-1) `(n0, n1)` is a state of the pair protocol `P`: both halves lie in
one clause's families `s·k + o`, at parameters the clause's relation admits. -/
def InP2 (P : Proto2) (n0 n1 : Nat) : Prop :=
  ∃ (c : Nat) (cl : Clause2) (k0 k1 : Nat), P.clauses[c]? = some cl ∧
    n0 = cl.s0 * k0 + cl.o0 ∧ n1 = cl.s1 * k1 + cl.o1 ∧ Rel2Holds cl.rel k0 k1

/-- (P4) The word with values `vs` holds its region: non-ghost, one number, in
a holding clause. -/
def WordHolds (P : Proto) (vs : List WeakMem.Val) : Prop :=
  P.ghost = false ∧ ∃ (n c : Nat) (cl : Clause) (k : Nat), vs = [.num n] ∧ P.clauses[c]? = some cl ∧
    cl.holds = true ∧ n = cl.scale * k + cl.off

/-- (P4) The pair with values `vs` holds its region: two numbers in a holding
clause. -/
def Word2Holds (P : Proto2) (vs : List WeakMem.Val) : Prop :=
  ∃ (n0 n1 c : Nat) (cl : Clause2) (k0 k1 : Nat), vs = [.num n0, .num n1] ∧ P.clauses[c]? = some cl ∧
    cl.holds = true ∧ n0 = cl.s0 * k0 + cl.o0 ∧ n1 = cl.s1 * k1 + cl.o1 ∧ Rel2Holds cl.rel k0 k1

/-- `VR ρ η t rt ws`: the words `ws`, carried at a runtime type of shape `rt`,
realise the static type `t` at `ρ` and `η`.  A pair must be a runtime pair,
split where its left component's layout ends; an index existential must be a
runtime package with some witness.  Other types are unconstrained until their
stage.  (The runtime side is a shape, not a type: see §2a.) -/
def VR (ρ : Nat → Nat) (η : TEnv) : Ty → Shp → List Word → Prop
  | .intS i, _, ws => ws.map (·.val) = [.num (ev ρ i)]
  | .int, _, ws => ∃ n, ws.map (·.val) = [.num n]
  | .tid, _, ws => ∃ l c, ws.map (·.val) = [.loc ⟨l, 0⟩ 0] ∧ η.sto l = some c ∧ c.ty = .unit ∧
      ModeOK η.tid η.pfr η.seen .pub l c ws
  | .fix sg w, rt, ws => rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w
  | .lanes sg w, rt, ws => rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]
  | .refine t ψ, rt, ws => VR ρ η t rt ws ∧ IniR ρ (η.selIni t) ψ ws
  | .iex b, rt, ws => ∃ n rb w, rt = .iex n rb ∧ VR (vcons w ρ) η b rb ws
  | .prod a b, rt, ws => ∃ ra rb, rt = .prod ra rb ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VR ρ η a ra (ws.take n) ∧ VR ρ η b rb (ws.drop n)
  -- T3c-5d: a boxed sum is a reference to a box whose payload, re-injected into
  -- the summand its tag (less the offset `s`) selects, is a value there; a boxed
  -- summand is read through the same reference, its tag offset further (`vsh`)
  | .sum a b, rt, ws => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VR ρ η a (vsh s (shp Ra)) ws) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VR ρ η.unsee a (shp Ra) q)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VR ρ η b (vsh (s + (armsOf Ra).length) (shp Rb)) ws) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VR ρ η.unsee b (shp Rb) q))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VR ρ η a (shp Ra) q) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VR ρ η b (shp Rb) q))
  | .tvar k, rt, ws => ∃ ws', WLe ws' ws ∧ η.get k rt ws'
  | .code σ τ, rt, ws => ∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy
  -- T3c-3: a reference's cell is in Σ, holds exactly the closure of the target
  -- type (invariant: no strong update), and agrees with the mode
  | .ptr μ u, _, ws => ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none
  -- F5: `null` is a locative only to a zero-length array (`zeroableIn`), which
  -- no access reaches (T3c-5a)
  | .loc μ u, _, ws => (ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U
  | .ptrOpt μ u, _, ws => ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none
  | .void, _, _ => False
  -- T3c: some closed witness `s`; its variable has no values (`push0`), which
  -- `guardT` keeps where `VR` reads only witnesses (code signatures, and from
  -- T3c-3 reference targets)
  | .tex κ b, rt, ws => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VR ρ (η.push0 s) b rb ws
  -- T3c-5a (notes §2a): the body, its variable the closed `μ` type itself; the
  -- variable is guarded (`guardT`), so its (empty, `push0`) relation is never
  -- read, and `VR` at a reference to it compares with the witness
  | .mu b, rt, ws => VR ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) b rt ws
  -- T3c-5f: indices are erased, so a value of `∀i. b` is, on the same words, a
  -- value of `b` at every index
  | .iall b, rt, ws => ∀ n, VR (vcons n ρ) η b rt ws
  -- T3d-1: a protocol word's protocol is well formed (`mkWord` checks it), and a
  -- runtime word holds a state of it
  | .word _ P, _, ws => pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)
  -- T3d-1: a protocol pair holds a pair state (`mkWord2`, `stp` and `casp`
  -- check one); an epoch pair holds two numbers (`caspE` writes the live
  -- token's epoch and an arbitrary value, so nothing stronger is invariant)
  | .word2 _ P, _, ws => pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1
  | .epair _ P, _, ws => pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]
  | _, _, _ => True

/-- (W1) The word key a token carries: a fresh token (`tok r none`, made by
`region`, consumed by `mkWord*`) carries its region's word. -/
def tokWd (n : Nat) : Option (Proto × Idx) → Res
  | none => .one (.wd n)
  | some _ => .zero

@[simp] theorem tokWd_none (n : Nat) : tokWd n none = .one (.wd n) := rfl
@[simp] theorem tokWd_some (n : Nat) (x : Proto × Idx) : tokWd n (some x) = .zero := rfl
@[simp] theorem tokWd_map (n : Nat) (o : Option (Proto × Idx)) (f : Proto × Idx → Proto × Idx) :
    tokWd n (o.map f) = tokWd n o := by cases o <;> rfl

/-- (W1) The word key a protocol word carries: its region's, unless it is an
epoch counter (no held state, `epoch_facts`; `mkTicket` makes an epoch
dispenser and a ticket owner from one token, and only the owner carries it). -/
def wdW (P : Proto) (n : Nat) : Res := if P.epoch then .zero else .one (.wd n)

@[simp] theorem wdW_epoch {P : Proto} (h : P.epoch = true) (n : Nat) : wdW P n = .zero := by simp [wdW, h]
@[simp] theorem wdW_nepoch {P : Proto} (h : P.epoch = false) (n : Nat) : wdW P n = .one (.wd n) := by
  simp [wdW, h]

/-- (F2′ A) The own-handle key a reference word carries: an `own` reference
to label `l` carries `own l`; a null one, and every other mode, nothing.  It
reads the words' values only. -/
def ownW (μ : Mode) (ws : List Word) : Res :=
  match μ, ws.map (·.val) with
  | .own, [WeakMem.Val.loc a _] => .one (.own a.label)
  | _, _ => .zero

@[simp] theorem ownW_pub (ws : List Word) : ownW .pub ws = .zero := rfl
@[simp] theorem ownW_rgn (r : Idx) (ws : List Word) : ownW (.rgn r) ws = .zero := rfl
theorem ownW_own_loc {ws : List Word} {a : WeakMem.Address} {g : Nat} (h : ws.map (·.val) = [.loc a g]) :
    ownW .own ws = .one (.own a.label) := by
  simp only [ownW, h]
theorem ownW_null (μ : Mode) {ws : List Word} (h : ws.map (·.val) = [.null]) : ownW μ ws = .zero := by
  cases μ <;> simp only [ownW, h]
theorem ownW_vals {μ : Mode} {ws ws' : List Word} (h : ws.map (·.val) = ws'.map (·.val)) :
    ownW μ ws = ownW μ ws' := by
  simp only [ownW, h]
@[simp] theorem ownW_shift (c : Nat) (μ : Mode) (ws : List Word) : ownW (μ.shift c) ws = ownW μ ws := by
  cases μ <;> rfl
@[simp] theorem ownW_inst (us : List Idx) (d : Nat) (μ : Mode) (ws : List Word) :
    ownW (instM us d μ) ws = ownW μ ws := by
  cases μ <;> rfl
@[simp] theorem ownW_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) (ws : List Word) :
    ownW (clM ρ d μ) ws = ownW μ ws := by
  cases μ <;> rfl
theorem ownW_meq {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEq cx d μ ν) (ws : List Word) :
    ownW μ ws = ownW ν ws := by
  cases h <;> rfl

/-- (T3d-2 A1) `VRR ρ η t rt ws R`: `VR`, with `R` the resources the value
carries, counted exactly: a token is one key, a pair the sum of its parts, a
sum its arm's, a package its body's at the witness, an array the sum of its
elements'.  Everything else carries none.  (W1) Every word or pair value,
and a fresh token, also carries its region's word key `wd`. -/
def VRR (ρ : Nat → Nat) (η : TEnv) : Ty → Shp → List Word → Res → Prop
  | .unit, _, _, R => R = .zero
  | .intS i, _, ws, R => ws.map (·.val) = [.num (ev ρ i)] ∧ R = .zero
  | .int, _, ws, R => (∃ n, ws.map (·.val) = [.num n]) ∧ R = .zero
  | .tid, _, ws, R => VR ρ η .tid (.leaf (some 1)) ws ∧ R = .zero
  | .fix sg w, rt, ws, R => (rt = .fix sg w ∧ ∃ n, ws.map (·.val) = [.num n] ∧ n < pw2 w) ∧ R = .zero
  | .lanes sg w, rt, ws, R => (rt = .lanes sg w ∧ ∃ n, ws.map (·.val) = [.num n]) ∧ R = .zero
  | .refine t ψ, rt, ws, R => VRR ρ η t rt ws R ∧ IniR ρ (η.selIni t) ψ ws
  | .iex b, rt, ws, R => ∃ n rb w, rt = .iex n rb ∧ VRR (vcons w ρ) η b rb ws R
  | .prod a b, rt, ws, R => ∃ ra rb, rt = .prod ra rb ∧ ∃ Ra Rb, R = Ra + Rb ∧
      (ra.wc = none → R = .zero) ∧ ∀ n, ra.wc = some n →
      n ≤ ws.length ∧ VRR ρ η a ra (ws.take n) Ra ∧ VRR ρ η b rb (ws.drop n) Rb
  | .sum a b, rt, ws, R => ∃ n Ra Rb, rt = .sum n (.sum Ra Rb) ∧
      (((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x s B, ws.map (·.val) = [.loc x 0] ∧ x.offset = 0 ∧
          η.box x.label = some B ∧ n = some (s + 1) ∧
          (s ≤ B.tag ∧ ((armsOf (.sum Ra Rb))[B.tag - s]?).bind wc = some B.pay.length) ∧
          ((η.seen x.label ∧ ∃ f, η.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) ∧
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VRR ρ η a (vsh s (shp Ra)) ws R) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) B.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VRR ρ η.unsee a (shp Ra) q R)) ∧
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VRR ρ η b (vsh (s + (armsOf Ra).length) (shp Rb)) ws R) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VRR ρ η.unsee b (shp Rb) q R))) ∨ ∃ j p,
        decodeArm (Ty.sum Ra Rb).tier (armsOf (.sum Ra Rb)) ws = some (j, p) ∧
        (j < (armsOf Ra).length → ∃ q, ofArm Ra j p = some q ∧ VRR ρ η a (shp Ra) q R) ∧
        ((armsOf Ra).length ≤ j → ∃ q, ofArm Rb (j - (armsOf Ra).length) p = some q ∧ VRR ρ η b (shp Rb) q R))
  | .tvar k, rt, ws, R => ∃ ws', WLe ws' ws ∧ η.rrs k rt ws' R
  | .code σ τ, _, ws, R => (∃ i d, ws.map (·.val) = [.num i] ∧ η.prog[i]? = some d ∧
      η.prog.find? (·.name == d.name) = some d ∧ d.tparams = [] ∧ d.idx = [] ∧
      cl ρ η.wit 0 0 σ = clD d.argTy ∧ cl ρ η.wit 0 0 τ = clD d.retTy) ∧ R = .zero
  | .ptr μ u, _, ws, R => (∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
      Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none) ∧ R = ownW μ ws
  | .loc μ u, _, ws, R => ((ws.map (·.val) = [.null] ∧ ∃ e, Fd (.array (.lit 0) e) (cl ρ η.wit 0 0 u)) ∨
      ∃ a c U, ws.map (·.val) = [.loc a 0] ∧ η.sto a.label = some c ∧
        AtOff c.ty a.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧
          IniAt (modeIni μ η.ini η.rini) c a U) ∧ R = ownW μ ws
  | .ptrOpt μ u, _, ws, R => (ws.map (·.val) = [.null] ∨
      ∃ a c, ws.map (·.val) = [.loc a 0] ∧ a.offset = 0 ∧ η.sto a.label = some c ∧
        Fd c.ty (cl ρ η.wit 0 0 u) ∧ ModeOK η.tid η.pfr η.seen μ a.label c ws ∧ accs c.ty ≠ none) ∧ R = ownW μ ws
  | .void, _, _, _ => False
  | .tex κ b, rt, ws, R => ∃ n rb s, rt = .tex n rb ∧ Clo s ∧ WitOK κ s ∧ VRR ρ (η.push0 s) b rb ws R
  | .mu b, rt, ws, R => VRR ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) b rt ws R
  | .iall b, rt, ws, R => ∀ n, VRR (vcons n ρ) η b rt ws R
  -- (P4) a word in a holding state holds its region's token
  | .word r P, _, ws, R => (pwf P = true ∧ (P.ghost = false → ∃ n, ws.map (·.val) = [.num n] ∧ InP P n)) ∧
      ((WordHolds P (ws.map (·.val)) ∧ R = .one (.rg (ev ρ r)) + wdW P (ev ρ r)) ∨
        (¬ WordHolds P (ws.map (·.val)) ∧ R = wdW P (ev ρ r)))
  | .word2 r P, _, ws, R => (pwf2 P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1] ∧ InP2 P n0 n1) ∧
      ((Word2Holds P (ws.map (·.val)) ∧ R = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r))) ∨
        (¬ Word2Holds P (ws.map (·.val)) ∧ R = .one (.wd (ev ρ r))))
  | .epair _ P, _, ws, R => (pwfE P = true ∧ ∃ n0 n1, ws.map (·.val) = [.num n0, .num n1]) ∧ R = .zero
  | .cap _ _, _, _, R => R = .zero
  | .tok r st, _, _, R => R = .one (.rg (ev ρ r)) + tokWd (ev ρ r) st
  | .tok2 r _ _ _, _, _, R => R = .one (.rg (ev ρ r))
  | .tokE r _ e, _, _, R => R = .one (.ep (ev ρ r) (ev ρ e))
  | .share r, _, _, R => R = .one (.sh (ev ρ r))
  -- an array is never a value (`accs` is `none`; `Ty.arrFree` keeps arrays
  -- behind a `Loc`), so this arm is unreachable; tokens in an
  -- array cell are counted per slot by the memory layer
  | .array _ _, _, _, R => R = .zero


/-- (T3d-2 A1) The resourceful relations refine the plain ones. -/
def RLink (η : TEnv) : Prop :=
  (∀ k S ws R, η.rrs k S ws R → η.rels k S ws) ∧ ∀ k S ws R, η.urrs k S ws R → η.urels k S ws

theorem RLink_push0 {η : TEnv} (h : RLink η) (s : Ty) : RLink (η.push0 s) := by
  constructor
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk ⊢; exact h.1 k S ws R hk
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk ⊢; exact h.2 k S ws R hk

theorem RLink_unsee {η : TEnv} (h : RLink η) : RLink η.unsee := ⟨h.2, h.2⟩

/-- (T3d-2 A1) The bridge: forgetting the resources, `VRR` is `VR`. -/
theorem VRR_VR : ∀ (t : Ty) {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word} {R : Res},
    RLink η → VRR ρ η t rt ws R → VR ρ η t rt ws := by
  intro t
  induction t with
  | refine t ψ ih => intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]; exact ⟨ih hl h.1, h.2⟩
  | iex b ih =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]
      obtain ⟨n, rb, w, e, h⟩ := h; exact ⟨n, rb, w, e, ih hl h⟩
  | prod a b iha ihb =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]
      obtain ⟨ra, rb, e, Ra, Rb, -, -, h⟩ := h
      exact ⟨ra, rb, e, fun n hn => let q := h n hn; ⟨q.1, iha hl q.2.1, ihb hl q.2.2⟩⟩
  | sum a b iha ihb =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]
      obtain ⟨n, Ra, Rb, e, h | ⟨j, p, hd, h1, h2⟩⟩ := h
      · obtain ⟨ht, x, s, B, h1, h2, h3, h4, h5, h6, hL, hR⟩ := h
        refine ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, h1, h2, h3, h4, h5, h6, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q1, q2⟩ := hL hj
          refine ⟨fun hb => iha hl (q1 hb), fun hb => ?_⟩
          obtain ⟨q, c1, c2, c3, c4, c5⟩ := q2 hb
          exact ⟨q, c1, c2, c3, c4, iha (RLink_unsee hl) c5⟩
        · obtain ⟨q1, q2⟩ := hR hj
          refine ⟨fun hb => ihb hl (q1 hb), fun hb => ?_⟩
          obtain ⟨q, c1, c2, c3, c4, c5⟩ := q2 hb
          exact ⟨q, c1, c2, c3, c4, ihb (RLink_unsee hl) c5⟩
      · refine ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, c1, c2⟩ := h1 hj; exact ⟨q, c1, iha hl c2⟩
        · obtain ⟨q, c1, c2⟩ := h2 hj; exact ⟨q, c1, ihb hl c2⟩
  | tvar k =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]
      obtain ⟨ws', hw, h⟩ := h; exact ⟨ws', hw, hl.1 k rt ws' R h⟩
  | tex κ b ih =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]
      obtain ⟨n, rb, s, e, hc, hk, h⟩ := h; exact ⟨n, rb, s, e, hc, hk, ih (RLink_push0 hl s) h⟩
  | mu b ih =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]; exact ih (RLink_push0 hl _) h
  | iall b ih =>
      intro ρ η rt ws R hl h; simp only [VRR] at h; simp only [VR]; exact fun n => ih hl (h n)
  | void => intro ρ η rt ws R _ h; simp only [VRR] at h
  | intS | int | tid | fix | lanes | code | ptr | loc | ptrOpt | word | word2 | epair =>
      intro ρ η rt ws R _ h; simp only [VRR] at h; simp only [VR]; exact h.1
  | unit | cap | tok | tok2 | tokE | share | array => intro ρ η rt ws R _ _; simp [VR]

/-! ### Structural lemmas: index shifts, type equality, instantiation -/

theorem decodeArm_wle {tr : Tier} {as : List Ty} {ws ws' : List Word} {j : Nat} {p : List Word}
    (e : WLe ws ws') (h : decodeArm tr as ws = some (j, p)) :
    ∃ p', decodeArm tr as ws' = some (j, p') ∧ WLe p p' := by
  cases tr with
  | boxed => simp [decodeArm] at h
  | niche =>
      rcases ws with _ | ⟨w, _ | ⟨w2, rest⟩⟩
      · simp [decodeArm] at h
      · obtain ⟨w', rfl, hw1⟩ := WLe_one e
        have ew : w'.val = w.val := hw1.1.symm
        simp only [decodeArm] at h ⊢
        rw [ew]
        cases hw : w.val with
        | loc a g =>
            rw [hw] at h
            cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
            | none => simp [h1, bind, Option.bind] at h
            | some pr =>
                simp [h1, bind, Option.bind, pure] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨[{ w' with val := .loc a 0 }], by simp [h1, bind, Option.bind, pure],
                  ⟨rfl, fun _ _ _ => hw1.2 a g hw⟩, trivial⟩
        | num k =>
            rw [hw] at h
            exact ⟨p, h, WLe_refl p⟩
        | _ => rw [hw] at h; simp at h
      · simp [decodeArm] at h
  | wide =>
      rcases ws with _ | ⟨t, _ | ⟨w, _ | ⟨w3, rest⟩⟩⟩
      · simp [decodeArm] at h
      · simp [decodeArm] at h
      · obtain ⟨t', w', rfl, ht1, hw1⟩ := WLe_two e
        have et : t'.val = t.val := ht1.1.symm
        simp only [decodeArm] at h ⊢
        rw [et]
        cases ht : t.val with
        | num k =>
            rw [ht] at h
            cases h1 : as[k]? with
            | none => simp [h1, bind, Option.bind] at h
            | some a =>
                simp only [h1, bind, Option.bind] at h ⊢
                by_cases hr : a.rawWords = some 0
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], ⟨rfl, rfl⟩, trivial⟩
                · simp [hr, pure] at h ⊢; obtain ⟨rfl, rfl⟩ := h; exact ⟨[w'], ⟨rfl, rfl⟩, hw1, trivial⟩
        | _ => rw [ht] at h; simp at h
      · simp [decodeArm] at h

theorem encodeArm_wle {tr : Tier} {as : List Ty} {j : Nat} {p p' q : List Word}
    (e : WLe p p') (h : encodeArm tr as j p = some q) :
    ∃ q', encodeArm tr as j p' = some q' ∧ WLe q q' := by
  cases tr with
  | boxed => simp [encodeArm] at h
  | wide =>
      match p, p', e, h with
      | [], [], _, h => exact ⟨q, h, WLe_refl q⟩
      | [w], [w'], e, h =>
          simp only [encodeArm, Option.some.injEq] at h; subst h
          exact ⟨_, rfl, WLe1_refl _, e.1, trivial⟩
      | _ :: _ :: _, _, _, h => simp [encodeArm] at h
      | [], _ :: _, e, _ => exact (e : False).elim
      | [_], [], e, _ => exact (e : False).elim
      | [_], _ :: _ :: _, e, _ => exact (e.2 : False).elim
  | niche =>
      simp only [encodeArm, bind, Option.bind] at h ⊢
      cases h1 : as[j]? with
      | none => simp [h1] at h
      | some a =>
          simp only [h1] at h ⊢
          match p, p', e, h with
          | [], [], _, h => exact ⟨q, h, WLe_refl q⟩
          | [w], [w'], e, h =>
              have ew : w'.val = w.val := e.1.1.symm
              cases hk : armK a with
              | ptr =>
                  simp only [hk] at h ⊢; rw [ew]
                  cases hw : w.val <;> simp only [hw] at h <;> simp at h
                  subst h; exact ⟨_, rfl, ⟨rfl, fun _ _ _ => e.1.2 _ _ hw⟩, trivial⟩
              | opt =>
                  simp only [hk] at h ⊢; rw [ew]
                  cases hw : w.val <;> simp only [hw] at h <;> simp at h
                  · subst h; exact ⟨_, rfl, ⟨rfl, fun _ _ _ => e.1.2 _ _ hw⟩, trivial⟩
                  · subst h; exact ⟨_, rfl, WLe_refl _⟩
              | nil => simp [hk] at h
              | wide => simp [hk] at h
          | _ :: _ :: _, _, _, h =>
              cases hk : armK a <;> simp [hk] at h
          | [], _ :: _, e, _ => exact (e : False).elim
          | [_], [], e, _ => exact (e : False).elim
          | [_], _ :: _ :: _, e, _ => exact (e.2 : False).elim

theorem ofArm_wle {t : Ty} {j : Nat} {p p' q : List Word} (e : WLe p p') (h : ofArm t j p = some q) :
    ∃ q', ofArm t j p' = some q' ∧ WLe q q' := by
  unfold ofArm at h ⊢
  split at h
  · rename_i hs; rw [if_pos hs]; exact encodeArm_wle e h
  · rename_i hs; rw [if_neg hs]
    split at h
    · simp at h; subst h; exact ⟨p', by simp_all, e⟩
    · simp at h

theorem asArm_wle {t : Ty} {ws ws' : List Word} {j : Nat} {p : List Word} (e : WLe ws ws')
    (h : asArm t ws = some (j, p)) : ∃ p', asArm t ws' = some (j, p') ∧ WLe p p' := by
  unfold asArm at h ⊢
  split at h
  · rename_i hs; rw [if_pos hs]; exact decodeArm_wle e h
  · rename_i hs; rw [if_neg hs]; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨ws', by simp, e⟩

/-- **`VR` reads values, and of views only that a `pub` reference's is past its
cell's frontier** (T3c-5c): so it survives the same values with pointer views
that only grow (`WLe`), which is what loads and stores do to pointer words. -/
theorem VR_up {ρ : Nat → Nat} {η : TEnv} : ∀ (t : Ty) (rt : Shp) (ws ws' : List Word),
    WLe ws ws' → VR ρ η t rt ws → VR ρ η t rt ws' := by
  intro t
  induction t generalizing ρ η with
  | tex κ b ih =>
      intro rt ws ws' e hv
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := hv
      exact ⟨n, rb, s, hr, hs, haf, ih rb ws ws' e hv⟩
  | prod a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, hr, hf⟩ := hv
      refine ⟨ra, rb, hr, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨e.length ▸ h1, iha ra _ _ (e.take n) h2, ihb rb _ _ (e.drop n) h3⟩
  | iex b ih =>
      intro rt ws ws' e hv
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := hv
      exact ⟨n, rb, w, hr, ih rb ws ws' e hv⟩
  | refine t ψ ih =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢; exact ⟨ih rt ws ws' e hv.1, IniR_vals e.vals ψ hv.2⟩
  | sum a b iha ihb =>
      intro rt ws ws' e hv
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · exact ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, e.vals.symm.trans hx, ho, hB, hn, hsB,
          hm.imp id (WLe_view e hx B.fr), fun hj => ⟨fun e' => iha _ _ _ e ((hA hj).1 e'), (hA hj).2⟩,
          fun hj => ⟨fun e' => ihb _ _ _ e ((hA' hj).1 e'), (hA' hj).2⟩⟩⟩
      · obtain ⟨p', hd', ep⟩ := decodeArm_wle e hd
        refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p', hd', fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', iha _ _ _ eq hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', ihb _ _ _ eq hv⟩
  | mu b ih => intro rt ws ws' e hv; simp only [VR] at hv ⊢; exact ih rt ws ws' e hv
  | iall b ih => intro rt ws ws' e hv; simp only [VR] at hv ⊢; exact fun n => ih rt ws ws' e (hv n)
  | tvar k =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢
      obtain ⟨w0, h0, hr⟩ := hv
      exact ⟨w0, WLe_trans h0 e, hr⟩
  | ptr μ u =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
        ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | ptrOpt μ u =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl (e.vals.symm.trans hn)
      · exact Or.inr ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
          ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | loc μ u =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨e.vals.symm.trans hn.1, hn.2⟩
      · exact Or.inr ⟨a, c, U, e.vals.symm.trans h1, h3, h4, hF,
          ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩
  | tid =>
      intro rt ws ws' e hv; simp only [VR] at hv ⊢
      obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
      exact ⟨l, c, e.vals.symm.trans h1, h2, h3,
        ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5⟩
  | _ => intro rt ws ws' e hv; simp only [VR] at hv ⊢ <;> first | exact hv | (rw [← e.vals]; exact hv)

/-- Words without pointers: `VR` reads only their values. -/
theorem VR_vals_nl {ρ : Nat → Nat} {η : TEnv} (t : Ty) (rt : Shp) {ws ws' : List Word} (e : VEq ws ws')
    (hn : ∀ w ∈ ws, ∀ a g, w.val ≠ .loc a g) (hv : VR ρ η t rt ws) : VR ρ η t rt ws' :=
  VR_up t rt ws ws' (WLe_of_vals e hn) hv

/-- **Shape agreement.**  `VR` cannot tell agreeing runtime types apart. -/
theorem VR_agree {ρ : Nat → Nat} {η : TEnv} {t r r' : Ty} {ws : List Word} (h : Agree r r')
    (hv : VR ρ η t (shp r) ws) : VR ρ η t (shp r') ws := h ▸ hv

theorem VR_shift (η : TEnv) : ∀ (t : Ty) (c w : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    VR (vins c w ρ) η (t.shiftI c) rt ws ↔ VR ρ η t rt ws
  | .intS i, c, w, ρ, _, _ => by simp [Ty.shiftI, VR, ev_shift]
  | .int, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .tid, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .fix _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .lanes _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .refine t ψ, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR]; exact and_congr (VR_shift η t c w ρ rt ws) (by rw [TEnv.selIni_shiftI]; exact IniR_shift c w ρ _ ws ψ)
  | .iex b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR]
      constructor
      · rintro ⟨n, rb, v, hr, hv⟩
        rw [← vins_succ] at hv
        exact ⟨n, rb, v, hr, (VR_shift η b (c + 1) w (vcons v ρ) rb ws).1 hv⟩
      · rintro ⟨n, rb, v, hr, hv⟩
        refine ⟨n, rb, v, hr, ?_⟩
        rw [← vins_succ]
        exact (VR_shift η b (c + 1) w (vcons v ρ) rb ws).2 hv
  | .prod a b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR, VR_shift η a c w ρ, VR_shift η b c w ρ]
  | .unit, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .void, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .sum a b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR, VR_shift η a c w ρ, VR_shift η b c w ρ, VR_shift η.unsee a c w ρ,
        VR_shift η.unsee b c w ρ]
  | .code a b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR, cl_vins]
  | .array _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .ptr _ _, _, _, _, _, _ => by simp only [Ty.shiftI, VR, cl_vins, ModeOK_shift]
  | .ptrOpt _ _, _, _, _, _, _ => by simp only [Ty.shiftI, VR, cl_vins, ModeOK_shift]
  | .loc _ _, _, _, _, _, _ => by simp only [Ty.shiftI, VR, cl_vins, ModeOK_shift, modeIni_shift, modeIni_shift]
  | .share _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .cap _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .word _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .tok _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .word2 _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .tok2 _ _ _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .epair _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .tokE _ _ _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .tvar _, _, _, _, _, _ => by simp [Ty.shiftI, VR]
  | .mu b, c, w, ρ, rt, ws => by
      have e := cl_vins c w ρ η.wit (.mu b)
      simp only [Ty.shiftI] at e
      simp only [Ty.shiftI, VR, e]
      exact VR_shift _ b c w ρ rt ws
  | .iall b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR]
      refine forall_congr' fun n => ?_
      rw [← vins_succ]
      exact VR_shift η b (c + 1) w (vcons n ρ) rt ws
  | .tex κ b, c, w, ρ, rt, ws => by
      simp only [Ty.shiftI, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_shift (η.push0 s) b c w ρ rb ws

/-- An integer of known index is the one word `num (ev ρ i)`. -/
theorem VR_intS {ρ : Nat → Nat} {η : TEnv} : ∀ {t : Ty} {rt : Shp} {i : Idx} {ws : List Word},
    intOf t = some (some i) → VR ρ η t rt ws → ws.map (·.val) = [.num (ev ρ i)]
  | .intS _, _, _, _, h, hv => by simp [intOf] at h; subst h; simpa [VR] using hv
  | .refine t _, _, _, _, h, hv => VR_intS (t := t) (by simpa [intOf] using h) (by simp only [VR] at hv; exact hv.1)
  | .int, _, _, _, h, _ => by simp [intOf] at h
  | .unit, _, _, _, h, _ => by simp [intOf] at h
  | .void, _, _, _, h, _ => by simp [intOf] at h
  | .prod _ _, _, _, _, h, _ => by simp [intOf] at h
  | .sum _ _, _, _, _, h, _ => by simp [intOf] at h
  | .code _ _, _, _, _, h, _ => by simp [intOf] at h
  | .array _ _, _, _, _, h, _ => by simp [intOf] at h
  | .ptr _ _, _, _, _, h, _ => by simp [intOf] at h
  | .ptrOpt _ _, _, _, _, h, _ => by simp [intOf] at h
  | .loc _ _, _, _, _, h, _ => by simp [intOf] at h
  | .share _, _, _, _, h, _ => by simp [intOf] at h
  | .cap _ _, _, _, _, h, _ => by simp [intOf] at h
  | .word _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tok _ _, _, _, _, h, _ => by simp [intOf] at h
  | .word2 _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tok2 _ _ _ _, _, _, _, h, _ => by simp [intOf] at h
  | .epair _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tokE _ _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tvar _, _, _, _, h, _ => by simp [intOf] at h
  | .mu _, _, _, _, h, _ => by simp [intOf] at h
  | .iall _, _, _, _, h, _ => by simp [intOf] at h
  | .iex _, _, _, _, h, _ => by simp [intOf] at h
  | .tex _ _, _, _, _, h, _ => by simp [intOf] at h

/-- Any integer is one `num` word. -/
theorem VR_int {ρ : Nat → Nat} {η : TEnv} : ∀ {t : Ty} {rt : Shp} {o : Option Idx} {ws : List Word},
    intOf t = some o → VR ρ η t rt ws → ∃ n, ws.map (·.val) = [.num n]
  | .intS _, _, _, _, _, hv => ⟨_, by simpa [VR] using hv⟩
  | .int, _, _, _, _, hv => by simpa [VR] using hv
  | .refine t _, _, _, _, h, hv => VR_int (t := t) (by simpa [intOf] using h) (by simp only [VR] at hv; exact hv.1)
  | .unit, _, _, _, h, _ => by simp [intOf] at h
  | .void, _, _, _, h, _ => by simp [intOf] at h
  | .prod _ _, _, _, _, h, _ => by simp [intOf] at h
  | .sum _ _, _, _, _, h, _ => by simp [intOf] at h
  | .code _ _, _, _, _, h, _ => by simp [intOf] at h
  | .array _ _, _, _, _, h, _ => by simp [intOf] at h
  | .ptr _ _, _, _, _, h, _ => by simp [intOf] at h
  | .ptrOpt _ _, _, _, _, h, _ => by simp [intOf] at h
  | .loc _ _, _, _, _, h, _ => by simp [intOf] at h
  | .share _, _, _, _, h, _ => by simp [intOf] at h
  | .cap _ _, _, _, _, h, _ => by simp [intOf] at h
  | .word _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tok _ _, _, _, _, h, _ => by simp [intOf] at h
  | .word2 _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tok2 _ _ _ _, _, _, _, h, _ => by simp [intOf] at h
  | .epair _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tokE _ _ _, _, _, _, h, _ => by simp [intOf] at h
  | .tvar _, _, _, _, h, _ => by simp [intOf] at h
  | .mu _, _, _, _, h, _ => by simp [intOf] at h
  | .iall _, _, _, _, h, _ => by simp [intOf] at h
  | .iex _, _, _, _, h, _ => by simp [intOf] at h
  | .tex _ _, _, _, _, h, _ => by simp [intOf] at h

/-- **Type equality preserves `VR`.**  At depth 0 index equalities are
entailed by the facts, so `ρ` must satisfy them; under a binder (`d ≥ 1`)
`IEq` is syntactic and any valuation works. -/
theorem VR_tyEq {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) :
    ∀ {η : TEnv} (ρ : Nat → Nat) (rt : Shp) (ws : List Word), (d = 0 → Sat cx.facts ρ) →
      (VR ρ η t rt ws ↔ VR ρ η u rt ws) := by
  induction h with
  | refl => intros; exact Iff.rfl
  | intS h =>
      intro η ρ rt ws hs
      unfold IEq at h
      rcases h with rfl | ⟨hd, he⟩
      · exact Iff.rfl
      · simp only [VR, he ρ (hs hd)]
  | prod _ _ ih1 ih2 =>
      intro η ρ rt ws hs
      simp only [VR]
      exact exists_congr fun ra => exists_congr fun rb => and_congr_right fun _ =>
        forall_congr' fun n => imp_congr_right fun _ => and_congr_right fun _ =>
          and_congr (ih1 ρ ra _ hs) (ih2 ρ rb _ hs)
  | iex _ ih =>
      intro η ρ rt ws _
      simp only [VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun w =>
        and_congr_right fun _ => ih (vcons w ρ) rb ws (fun h => absurd h (Nat.succ_ne_zero _))
  | refine h' ih => intro η ρ rt ws hs; simp only [VR]; exact and_congr (ih ρ rt ws hs) (by rw [TEnv.selIni_tyEq η h'])
  | refineIni h h' ih =>
      intro η ρ rt ws hs
      simp only [VR]
      refine and_congr (ih ρ rt ws hs) ?_
      rw [TEnv.selIni_tyEq η h']
      unfold IEq at h
      rcases h with rfl | ⟨hd, he⟩
      · exact Iff.rfl
      · simp only [IniR, he ρ (hs hd)]
  | sum _ _ ih1 ih2 =>
      intro η ρ rt ws hs
      have e1 := fun rt ws => ih1 (η := η) ρ rt ws hs
      have e2 := fun rt ws => ih2 (η := η) ρ rt ws hs
      have e3 := fun rt ws => ih1 (η := η.unsee) ρ rt ws hs
      have e4 := fun rt ws => ih2 (η := η.unsee) ρ rt ws hs
      simp only [VR, e1, e2, e3, e4]
  | code h1 h2 _ _ =>
      intro η ρ rt ws hs
      simp only [VR, cl_tyEq0 h1 η.wit 0 hs, cl_tyEq0 h2 η.wit 0 hs]
  | array => intros; simp [VR]
  | ptr hm h _ =>
      intro η ρ rt ws hs
      simp only [VR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm]
  | ptrOpt hm h _ =>
      intro η ρ rt ws hs
      simp only [VR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm]
  | loc hm h _ =>
      intro η ρ rt ws hs
      simp only [VR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm, modeIni_meq hm]
  | word => intros; simp [VR]
  | word2 => intros; simp [VR]
  | tok2 => intros; simp [VR]
  | epair => intros; simp [VR]
  | tokE => intros; simp [VR]
  | tokNone => intros; simp [VR]
  | tokSome => intros; simp [VR]
  | share => intros; simp [VR]
  | cap => intros; simp [VR]
  | mu h ih =>
      intro η ρ rt ws hs
      simp only [VR, cl_tyEq0 (TyEqS.mu h) η.wit 0 hs]
      exact ih ρ rt ws hs
  | tex _ ih =>
      intro η ρ rt ws hs; simp only [VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => ih ρ rb ws hs
  | iall _ ih =>
      intro η ρ rt ws _
      simp only [VR]
      exact forall_congr' fun n => ih (vcons n ρ) rt ws (fun h => absurd h (Nat.succ_ne_zero _))

/-- **Subsumption preserves `VR`** (same runtime type and words: every `SubS`
case is representation-preserving). -/
theorem VR_sub {cx : Cx} {η : TEnv} {ρ : Nat → Nat} (hs : Sat cx.facts ρ) {σ τ : Ty}
    (h : SubS cx σ τ) : ∀ rt ws, VR ρ η σ rt ws → VR ρ η τ rt ws := by
  induction h generalizing η with
  | eq h => intro rt ws hv; exact (VR_tyEq h ρ rt ws (fun _ => hs)).1 hv
  | intS => intro rt ws hv; simp only [VR] at hv ⊢; exact ⟨_, hv⟩
  | refine _ ih => intro rt ws hv; simp only [VR] at hv; exact ih rt ws hv.1
  | iniWeak h hl =>
      intro rt ws hv; simp only [VR, IniR] at hv ⊢
      exact ⟨(VR_tyEq h ρ rt ws (fun _ => hs)).1 hv.1, fun a ha =>
        Nat.le_trans (hl ρ hs) (by rw [← TEnv.selIni_tyEq η h]; exact hv.2 a ha)⟩
  | prod _ _ iha ihb =>
      intro rt ws hv
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, hr, hf⟩ := hv
      refine ⟨ra, rb, hr, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨h1, iha _ _ h2, ihb _ _ h3⟩
  | nonNull hm h =>
      intro rt ws hv
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      refine Or.inr ⟨a, c, h1, h2, h3, (cl_tyEq0 h η.wit 0 (fun _ => hs)) ▸ h4, ?_, h6⟩
      rw [← ModeOK_meq (i := η.tid) hm]; exact h5
  | sum _ _ iha ihb =>
      intro rt ws hv
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · refine ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm,
          fun hj => ⟨fun e => iha _ _ ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => ihb _ _ ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e; exact ⟨q, hq, hs1, hw1, hv1, iha (η := η.unsee) _ _ hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e; exact ⟨q, hq, hs1, hw1, hv1, ihb (η := η.unsee) _ _ hv⟩
      · refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj; exact ⟨q, hq, iha _ _ hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, ihb _ _ hv⟩
  | cap => intros; simp [VR]

/-- **Index instantiation.**  `VR` at `t[w/d]` is `VR` at `t` with `w`'s value
inserted at `d`. -/
theorem VR_instT (w : Idx) (η : TEnv) :
    ∀ (t : Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
      VR ρ η (instT [w] d t) rt ws ↔ VR (vins d (ev (fun k => ρ (k + d)) w) ρ) η t rt ws
  | .intS i, d, ρ, _, _ => by simp [instT, VR, ev_instI]
  | .int, _, _, _, _ => by simp [instT, VR]
  | .tid, _, _, _, _ => by simp [instT, VR]
  | .fix _ _, _, _, _, _ => by simp [instT, VR]
  | .lanes _ _, _, _, _, _ => by simp [instT, VR]
  | .refine t ψ, d, ρ, rt, ws => by
      simp only [instT, VR]; exact and_congr (VR_instT w η t d ρ rt ws) (by rw [TEnv.selIni_instT]; exact IniR_inst w d ρ _ ws ψ)
  | .iex b, d, ρ, rt, ws => by
      have e : ∀ v, vins (d + 1) (ev (fun k => vcons v ρ (k + (d + 1))) w) (vcons v ρ) =
          vcons v (vins d (ev (fun k => ρ (k + d)) w) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vins_succ]
      simp only [instT, VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      rw [VR_instT w η b (d + 1) (vcons v ρ) rb ws, e v]
  | .prod a b, d, ρ, rt, ws => by
      simp only [instT, VR, VR_instT w η a d ρ, VR_instT w η b d ρ]
  | .unit, _, _, _, _ => by simp [instT, VR]
  | .void, _, _, _, _ => by simp [instT, VR]
  | .sum a b, d, ρ, rt, ws => by
      simp only [instT, VR, VR_instT w η a d ρ, VR_instT w η b d ρ, VR_instT w η.unsee a d ρ,
        VR_instT w η.unsee b d ρ]
  | .code a b, d, ρ, rt, ws => by
      simp only [instT, VR, cl_inst1]
  | .array _ _, _, _, _, _ => by simp [instT, VR]
  | .ptr _ _, _, _, _, _ => by simp only [instT, VR, cl_inst1, ModeOK_inst]
  | .ptrOpt _ _, _, _, _, _ => by simp only [instT, VR, cl_inst1, ModeOK_inst]
  | .loc _ _, _, _, _, _ => by simp only [instT, VR, cl_inst1, ModeOK_inst, modeIni_inst, modeIni_inst]
  | .share _, _, _, _, _ => by simp [instT, VR]
  | .cap _ _, _, _, _, _ => by simp [instT, VR]
  | .word _ _, _, _, _, _ => by simp [instT, VR]
  | .tok _ _, _, _, _, _ => by simp [instT, VR]
  | .word2 _ _, _, _, _, _ => by simp [instT, VR]
  | .tok2 _ _ _ _, _, _, _, _ => by simp [instT, VR]
  | .epair _ _, _, _, _, _ => by simp [instT, VR]
  | .tokE _ _ _, _, _, _, _ => by simp [instT, VR]
  | .tvar _, _, _, _, _ => by simp [instT, VR]
  | .mu b, d, ρ, rt, ws => by
      have e := cl_inst1 w d ρ η.wit (.mu b)
      simp only [instT] at e
      simp only [instT, VR, e]
      exact VR_instT w _ b d ρ rt ws
  | .iall b, d, ρ, rt, ws => by
      have e : ∀ v, vins (d + 1) (ev (fun k => vcons v ρ (k + (d + 1))) w) (vcons v ρ) =
          vcons v (vins d (ev (fun k => ρ (k + d)) w) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vins_succ]
      simp only [instT, VR]
      refine forall_congr' fun v => ?_
      rw [VR_instT w η b (d + 1) (vcons v ρ) rt ws, e v]
  | .tex κ b, d, ρ, rt, ws => by
      simp only [instT, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_instT w (η.push0 s) b d ρ rb ws

/-! ### Type shifts: a variable inserted at `c` that nothing mentions -/

theorem VR_shiftTU : ∀ (t : Ty) (c : Nat) (η : TEnv) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop)
    (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    VR ρ (η.insR c R s UR) (t.shiftT c) rt ws ↔ VR ρ η t rt ws
  | .tvar k, c, η, R, s, UR, ρ, rt, ws => by
      by_cases h : k ≥ c
      · have h1 : ¬ k + 1 < c := by omega
        have h2 : k + 1 ≠ c := by omega
        simp [Ty.shiftT, h, VR, TEnv.get, TEnv.insR, h1, h2]
      · have h1 : k < c := by omega
        simp [Ty.shiftT, h, VR, TEnv.get, TEnv.insR, h1]
  | .intS i, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .int, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .tid, _, _, _, _, _, _, _, _ => by simp only [Ty.shiftT, VR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen]
  | .fix _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .lanes _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .refine t ψ, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR, TEnv.insR_ini]; exact and_congr (VR_shiftTU t c η R s UR ρ rt ws) (by rw [TEnv.selIni_shiftT_insR])
  | .iex b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun v => and_congr_right fun _ =>
        VR_shiftTU b c η R s UR (vcons v ρ) rb ws
  | .prod a b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR, VR_shiftTU a c η R s UR ρ, VR_shiftTU b c η R s UR ρ]
  | .sum a b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR, VR_shiftTU a c η R s UR ρ, VR_shiftTU b c η R s UR ρ, unsee_insR,
        VR_shiftTU a c η.unsee UR s UR ρ, VR_shiftTU b c η.unsee UR s UR ρ, TEnv.insR_box, TEnv.insR_tid, TEnv.insR_seen, TEnv.insR_pfr]
  | .code a b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR, cl_insR, TEnv.insR_prog]
  | .tex κ b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun s' => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [← insR_push0 (UR := UR)]; exact VR_shiftTU b (c + 1) (η.push0 s') R s UR ρ rb ws
  | .unit, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .void, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .array _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .ptr _ _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen, TEnv.insR_pfr, TEnv.insR_seen]
  | .ptrOpt _ _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen, TEnv.insR_pfr, TEnv.insR_seen]
  | .loc _ _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen, TEnv.insR_ini, TEnv.insR_rini]
  | .share _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .cap _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .word _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .tok _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .word2 _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .epair _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .tokE _ _ _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VR]
  | .mu b, c, η, R, s, UR, ρ, rt, ws => by
      have e := cl_insR c R s η ρ (.mu b) UR
      simp only [Ty.shiftT] at e
      simp only [Ty.shiftT, VR, e]
      rw [← insR_push0 (UR := UR)]; exact VR_shiftTU b (c + 1) _ R s UR ρ rt ws
  | .iall b, c, η, R, s, UR, ρ, rt, ws => by
      simp only [Ty.shiftT, VR]
      exact forall_congr' fun v => VR_shiftTU b c η R s UR (vcons v ρ) rt ws

theorem VR_shiftT (t : Ty) (c : Nat) (η : TEnv) (R : Shp → List Word → Prop) (s : Ty)
    (ρ : Nat → Nat) (rt : Shp) (ws : List Word) :
    VR ρ (η.insR c R s) (t.shiftT c) rt ws ↔ VR ρ η t rt ws :=
  VR_shiftTU t c η R s _ ρ rt ws

theorem VR_shiftTN (σ : Ty) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) : ∀ (P : List Ty) (η : TEnv),
    VR ρ (TEnv.pre P η) (shiftTN P.length σ) rt ws ↔ VR ρ η σ rt ws
  | [], _ => Iff.rfl
  | s :: P, η => by
      show VR ρ ((TEnv.pre P η).insR 0 (fun _ _ => False) s) (Ty.shiftT 0 (shiftTN P.length σ)) rt ws ↔ _
      rw [VR_shiftT]; exact VR_shiftTN σ ρ rt ws P η

/-- `guardT` is stricter than CoreLang's guard (`unguarded`), which also counts
`Code` as one. -/
theorem unguarded_of_guardT {k : Nat} {t : Ty} (h : t.guardT k = true) : t.unguarded k = false := by
  induction t generalizing k with
  | tvar j => simp only [Ty.guardT, Ty.unguarded] at h ⊢; simpa using h
  | _ => simp_all [Ty.guardT, Ty.unguarded]

/-- **A guarded variable's relation is never read** (24e, T3c): where
`c` is not `unguarded` (as `guardT c` implies; T3c-5a: CoreLang's guard, so that
`μ` bodies qualify), variable `c` occurs only under references and in code
signatures, where `VR` reads witnesses, not relations. -/
theorem VR_relsG : ∀ (t : Ty) (c : Nat) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    t.unguarded c = false → (∀ k, k ≠ c → η₁.rels k = η₂.rels k) → (∀ k, k ≠ c → η₁.urels k = η₂.urels k) →
      η₁.wit = η₂.wit → CE η₁ = CE η₂ →
      (VR ρ η₁ t rt ws ↔ VR ρ η₂ t rt ws)
  | .tvar k, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, _, _ => by
      have hk : k ≠ c := by simpa [Ty.unguarded] using hg
      simp only [VR, TEnv.get, hr k hk]
  | .refine t ψ, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      have e3 : η₁.ini = η₂.ini := by have h := congrArg TEnv.ini hp; exact h
      simp only [VR, e3]; exact and_congr (VR_relsG t c η₁ η₂ ρ rt ws hg hr hur hw hp)
        (by rw [TEnv.selIni_eq hw e3 (by have h := congrArg TEnv.rini hp; exact h) t])
  | .iex b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun w => and_congr_right fun _ =>
        VR_relsG b c η₁ η₂ (vcons w ρ) rb ws hg hr hur hw hp
  | .prod a b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      have ha : ∀ rt ws, VR ρ η₁ a rt ws ↔ VR ρ η₂ a rt ws :=
        fun rt ws => VR_relsG a c η₁ η₂ ρ rt ws hg.1 hr hur hw hp
      have hb : ∀ rt ws, VR ρ η₁ b rt ws ↔ VR ρ η₂ b rt ws :=
        fun rt ws => VR_relsG b c η₁ η₂ ρ rt ws hg.2 hr hur hw hp
      simp only [VR, ha, hb]
  | .sum a b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      have ha : ∀ rt ws, VR ρ η₁ a rt ws ↔ VR ρ η₂ a rt ws :=
        fun rt ws => VR_relsG a c η₁ η₂ ρ rt ws hg.1 hr hur hw hp
      have hb : ∀ rt ws, VR ρ η₁ b rt ws ↔ VR ρ η₂ b rt ws :=
        fun rt ws => VR_relsG b c η₁ η₂ ρ rt ws hg.2 hr hur hw hp
      have hpu : CE η₁.unsee = CE η₂.unsee := by rw [← CE_unsee, ← CE_unsee, hp]
      have ha' : ∀ rt ws, VR ρ η₁.unsee a rt ws ↔ VR ρ η₂.unsee a rt ws :=
        fun rt ws => VR_relsG a c η₁.unsee η₂.unsee ρ rt ws hg.1 hur hur hw hpu
      have hb' : ∀ rt ws, VR ρ η₁.unsee b rt ws ↔ VR ρ η₂.unsee b rt ws :=
        fun rt ws => VR_relsG b c η₁.unsee η₂.unsee ρ rt ws hg.2 hur hur hw hpu
      have e1 : η₁.box = η₂.box := by have h := congrArg TEnv.box hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e3 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      simp only [VR, ha, hb, ha', hb', e1, e2, e3, e4]
  | .code a b, _, η₁, η₂, ρ, rt, ws, _, _, _, hw, hp => by
      have e : η₁.prog = η₂.prog := by have h := congrArg TEnv.prog hp; exact h
      simp only [VR, hw, e]
  | .tex κ b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_relsG b (c + 1) (η₁.push0 s) (η₂.push0 s) ρ rb ws hg ?_ ?_ ?_ hp
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hr k this]
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hur k this]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .intS _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .int, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .tid, _, η₁, η₂, _, _, _, _, _, _, _, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e3 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      simp only [VR, e1, e2, e3, e4]
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .unit, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .void, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .ptr _ _, _, η₁, η₂, ρ, rt, ws, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      simp only [VR, hw, e1, e2, e4, e5]
  | .ptrOpt _ _, _, η₁, η₂, ρ, rt, ws, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      simp only [VR, hw, e1, e2, e4, e5]
  | .loc _ _, _, η₁, η₂, ρ, rt, ws, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e3 : η₁.ini = η₂.ini := by have h := congrArg TEnv.ini hp; exact h
      have e3' : η₁.rini = η₂.rini := by have h := congrArg TEnv.rini hp; exact h
      simp only [VR, hw, e1, e2, e3, e3', e4, e5]
  | .share _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .mu b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VR, hw]
      refine VR_relsG b (c + 1) _ _ ρ rt ws hg ?_ ?_ ?_ hp
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hr k this]
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hur k this]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, c, η₁, η₂, ρ, rt, ws, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VR]
      exact forall_congr' fun n => VR_relsG b c η₁ η₂ (vcons n ρ) rt ws hg hr hur hw hp

/-- **Σ-monotonicity** (T3c-3): `VR` survives a larger store typing and larger
relations.  (`publish` changes a cell's owner: the one non-monotone step, which
consumes the only `own` reference.) -/
theorem VR_mono : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    VR ρ η₁ t rt ws → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VR ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VR, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢; exact ⟨VR_mono t η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR_mono b η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VR_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx e2, VR_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VR_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VR_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_mono a η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_mono b η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VR_mono a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj; exact ⟨q, hq, VR_mono b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
  | .code a b, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR_mono b (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .tid, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hv, _ => by
        simp only [VR] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simp [VR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, hv, hri => by simpa only [VR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hP, hS, hBx, _, hri => by simp [VR]
  | .mu b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      rw [← hw]
      refine VR_mono b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VR] at hv ⊢
      exact fun n => VR_mono b η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx (hv n)

/-- (D3) Every pointer word of `ws` has view at least `V`. -/
def LocAbove (V : WeakMem.Ts) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∀ a g, w.val = .loc a g → V ≤ w.view

theorem LocAbove.take {V : WeakMem.Ts} {ws : List Word} (n : Nat) (h : LocAbove V ws) : LocAbove V (ws.take n) :=
  fun w hw => h w (List.mem_of_mem_take hw)

theorem LocAbove.drop {V : WeakMem.Ts} {ws : List Word} (n : Nat) (h : LocAbove V ws) : LocAbove V (ws.drop n) :=
  fun w hw => h w (List.mem_of_mem_drop hw)

theorem LocAbove_decodeArm {V : WeakMem.Ts} {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (hd : decodeArm tr as ws = some (j, p)) (h : LocAbove V ws) : LocAbove V p := by
  intro x hx a g hxa
  unfold decodeArm at hd
  split at hd
  · rename_i w
    split at hd
    · rename_i a' g' hw
      cases hf : ((CoreTerm.enumFrom as 0).filter (fun p => isPtrish p.2))[g']? with
      | none => simp [hf] at hd
      | some jp =>
          simp only [hf, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hd
          obtain ⟨-, rfl⟩ := hd
          simp only [List.mem_singleton] at hx; subst hx
          exact h w (by simp) a' g' hw
    · rename_i _ jn _
      cases ha : as[jn]? with
      | none => simp [ha] at hd
      | some arm =>
          simp only [ha, Option.bind_eq_bind, Option.bind_some] at hd
          split at hd
          · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨-, rfl⟩ := hd; simp at hx
          · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨-, rfl⟩ := hd
            simp only [List.mem_singleton] at hx; subst hx; simp [cst, Promises.TVal.mk0] at hxa
          · cases hd
    · cases hd
  · rename_i t w
    split at hd
    · rename_i _ jn _
      cases ha : as[jn]? with
      | none => simp [ha] at hd
      | some arm =>
          simp only [ha, Option.bind_eq_bind, Option.bind_some] at hd
          split at hd
          · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨-, rfl⟩ := hd; simp at hx
          · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨-, rfl⟩ := hd
            simp only [List.mem_singleton] at hx; subst hx
            exact h x (by simp) a g hxa
    · cases hd
  · cases hd

theorem LocAbove_encodeArm {V : WeakMem.Ts} {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (he : encodeArm tr as j p = some q) (h : LocAbove V p) : LocAbove V q := by
  intro x hx a g hxa
  unfold encodeArm at he
  split at he
  · cases ha : as[j]? with
    | none => simp [ha] at he
    | some arm =>
        simp only [ha, Option.bind_eq_bind, Option.bind_some] at he
        split at he
        · split at he
          · rename_i a' g' hw
            simp only [Option.some.injEq] at he; subst he
            simp only [List.mem_singleton] at hx; subst hx
            simp only [LocAbove, List.mem_singleton, forall_eq] at h; exact h a' g' hw
          · split at he
            · simp only [Option.some.injEq] at he; subst he
              simp only [List.mem_singleton] at hx; subst hx; simp [cst, Promises.TVal.mk0] at hxa
            · cases he
          · cases he
        · split at he
          · rename_i a' g' hw
            simp only [Option.some.injEq] at he; subst he
            simp only [List.mem_singleton] at hx; subst hx
            simp only [LocAbove, List.mem_singleton, forall_eq] at h; exact h a' g' hw
          · split at he
            · simp only [Option.some.injEq] at he; subst he
              simp only [List.mem_singleton] at hx; subst hx; simp [cst, Promises.TVal.mk0] at hxa
            · cases he
          · cases he
        · simp only [Option.some.injEq] at he; subst he
          simp only [List.mem_singleton] at hx; subst hx; simp [cst, Promises.TVal.mk0] at hxa
        · cases he
  · split at he
    · simp only [Option.some.injEq] at he; subst he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [cst, Promises.TVal.mk0] at hxa
    · simp only [Option.some.injEq] at he; subst he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp [cst, Promises.TVal.mk0] at hxa
      · simp only [LocAbove, List.mem_singleton, forall_eq] at h; exact h a g hxa
    · cases he
  · cases he

theorem LocAbove_ofArm {V : WeakMem.Ts} {t : Ty} {j : Nat} {p q : List Word}
    (he : ofArm t j p = some q) (h : LocAbove V p) : LocAbove V q := by
  unfold ofArm at he
  split at he
  · exact LocAbove_encodeArm he h
  · split at he
    · simp only [Option.some.injEq] at he; subst he; exact h
    · cases he

/-- (D3) `ModeOK` forgetting `seen` at labels whose frontier is at most `V`,
for a pointer word of view at least `V`. -/
theorem ModeOK_unsee {i : Nat} {P P' : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S S' : WeakMem.AllocLabel → Prop} {V : WeakMem.Ts}
    (hP : ∀ l f, P l = some f → P' l = some f)
    (hS : ∀ l, S l → S' l ∨ ∃ f, P l = some f ∧ f ≤ V)
    {μ : Mode} {l : WeakMem.AllocLabel} {c : Cell} {ws : List Word} {a : WeakMem.Address}
    (hw : ws.map (·.val) = [.loc a 0]) (hL : LocAbove V ws) :
    ModeOK i P S μ l c ws → ModeOK i P' S' μ l c ws := by
  cases μ with
  | own => exact id
  | pub =>
    rintro ⟨f, h1, h2 | h2⟩
    · rcases hS l h2 with h3 | ⟨f', h3, h4⟩
      · exact ⟨f, hP l f h1, Or.inl h3⟩
      · rw [h1, Option.some.injEq] at h3; subst h3
        refine ⟨f, hP l f h1, Or.inr fun w hw' => Nat.le_trans h4 (hL w hw' a 0 ?_)⟩
        have : w.val ∈ ws.map (·.val) := List.mem_map_of_mem hw'
        rw [hw] at this; simpa using this
    · exact ⟨f, hP l f h1, Or.inr h2⟩
  | rgn _ => exact id



/-- (T3c-6 prep) The box clause of `VR` survives `unsee` for a word above
every seen frontier. -/
theorem boxSeen_unsee {η₁ η₂ : TEnv} {V : WeakMem.Ts} {ws : List Word} {x : WeakMem.Address} {B : Box}
    (hP : ∀ l f, η₁.pfr l = some f → η₂.pfr l = some f)
    (hS : ∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V)
    (hx : ws.map (·.val) = [.loc x 0]) (hL : LocAbove V ws)
    (hm : (η₁.seen x.label ∧ ∃ f, η₁.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view) :
    (η₂.seen x.label ∧ ∃ f, η₂.pfr x.label = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ ws, B.fr ≤ w.view := by
  rcases hm with ⟨h1, f, h2, h3⟩ | h
  · rcases hS _ h1 with h4 | ⟨f', h5, h6⟩
    · exact Or.inl ⟨h4, f, hP _ _ h2, h3⟩
    · rw [h2] at h5; cases h5
      refine Or.inr fun w hw => Nat.le_trans h3 (Nat.le_trans h6 (hL w hw x 0 ?_))
      have hm : w.val ∈ ws.map (·.val) := List.mem_map.2 ⟨w, hw, rfl⟩
      rw [hx] at hm; simpa using hm
  · exact Or.inr h

/-- (D3) **Forgetting `seen`**: `VR` survives dropping `seen` at labels whose
frontier is at most `V`, for words whose pointers all have view at least `V`. -/
theorem VR_unsee (V : WeakMem.Ts) : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
    (∀ k S vs, η₁.rels k S vs → η₂.rels k S vs) → (∀ k S vs, η₁.urels k S vs → η₂.urels k S vs) → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l ∨ ∃ f, η₁.pfr l = some f ∧ f ≤ V) →
    (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    LocAbove V ws → VR ρ η₁ t rt ws → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VR ρ η₂ t rt ws
  | .tvar k, η₁, η₂, ρ, rt, ws, hr, hur, _, _, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VR, TEnv.get] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      exact ⟨VR_unsee V t η₁ η₂ ρ rt ws hr hur hw hp ht hs hi hP hS hBx hL hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR_unsee V b η₁ η₂ (vcons w ρ) rb ws hr hur hw hp ht hs hi hP hS hBx hL h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VR_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.take n) e2,
        VR_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (hL.drop n) e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, boxSeen_unsee hP hS hx hL hm,
          fun hj => ⟨fun e => VR_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VR_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx hL ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_mono a η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VR_mono b η₁.unsee η₂.unsee ρ _ _ hur hur hw hp ht hs hi hP (fun _ h => h.elim) hBx hv⟩
      · have hLp := LocAbove_decodeArm hd hL
        refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          exact ⟨q, hq, VR_unsee V a η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj
          exact ⟨q, hq, VR_unsee V b η₁ η₂ ρ _ _ hr hur hw hp ht hs hi hP hS hBx (LocAbove_ofArm hq hLp) hv⟩
  | .code a b, η₁, η₂, ρ, rt, ws, _, _, hw, hp, _, _, _, _, _, hBx, _, hv, hri => by
      simp only [VR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR_unsee V b (η₁.push0 s) (η₂.push0 s) ρ rb ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      obtain ⟨a, c, h1, h2, h3, h4, h5, h6⟩ := hv
      exact ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_unsee hP hS h1 hL h5, h6⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, _, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl hn
      · exact Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_unsee hP hS h1 hL h5, h6⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      rcases hv with hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩
      · exact Or.inl ⟨hn.1, hw ▸ hn.2⟩
      · exact Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK_unsee hP hS h1 hL h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .tid, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hL, hv, _ => by
        simp only [VR] at hv ⊢
        obtain ⟨l, c, h1, h2, h3, h5⟩ := hv
        exact ⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOK_unsee hP hS h1 hL h5⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simp [VR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, hv, hri => by simpa only [VR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBx, _, _, hri => by simp [VR]
  | .mu b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      rw [← hw]
      refine VR_unsee V b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws
        (push0_rels_mono hr) (push0_urels_mono hur) ?_ hp ht hs hi hP hS hBx hL hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hL, hv, hri => by
      simp only [VR] at hv ⊢
      exact fun n => VR_unsee V b η₁ η₂ (vcons n ρ) rt ws hr hur hw hp ht hs hi hP hS hBx hL (hv n)

/-! ### Closing (T3c): `VR` at a type is `VR` at its closure -/


/-- **Coherence of `η`** (T3c): every witness is closed, and every variable
denotes exactly its witness's values (read in `CE η`, at any valuation).  The
package witnesses inside `VR` (`push0`) are not coherent: `VR_close` carries
them in the prefix `pre P`. -/
def Coh (η : TEnv) : Prop :=
  ∀ k, Clo (η.wit k) ∧ (∀ (ρ' : Nat → Nat) (S : Shp) (ws : List Word),
    η.rels k S ws ↔ VR ρ' (CE η) (η.wit k) S ws) ∧ ∀ (ρ' : Nat → Nat) (S : Shp) (ws : List Word),
    η.urels k S ws ↔ VR ρ' (CE η.unsee) (η.wit k) S ws


/-- (T3d-2 A1) `VR` does not read the resourceful relations. -/
theorem VR_insR_rr {ρ : Nat → Nat} {η : TEnv} {c : Nat} {R UR : Shp → List Word → Prop} {s : Ty}
    {RR URR : Shp → List Word → Res → Prop} {t : Ty} {rt : Shp} {ws : List Word} :
    VR ρ (η.insR c R s UR RR URR) t rt ws ↔ VR ρ (η.insR c R s UR) t rt ws :=
  ⟨fun hv => VR_mono t (η.insR c R s UR RR URR) (η.insR c R s UR) ρ rt ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h) hv,
    fun hv => VR_mono t (η.insR c R s UR) (η.insR c R s UR RR URR) ρ rt ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
      (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h) hv⟩

/-- (T3c-5d) A coherent view's memory view is coherent. -/
theorem Coh.unsee {η : TEnv} (hc : Coh η) : Coh η.unsee := fun k =>
  ⟨(hc k).1, (hc k).2.2, (hc k).2.2⟩

/-- A type with no free type variables does not see a prefix of binders. -/
theorem VR_pre_tb {s : Ty} (hs : tb 0 s = true) (ρ : Nat → Nat) (S : Shp) (ws : List Word) :
    ∀ (P : List Ty) (η : TEnv), VR ρ (TEnv.pre P η) s S ws ↔ VR ρ η s S ws
  | [], _ => Iff.rfl
  | s' :: P, η => by
      have e : s.shiftT 0 = s := tb_shiftT s hs (Nat.le_refl 0)
      have h := VR_shiftT s 0 (TEnv.pre P η) (fun _ _ => False) s' ρ S ws
      rw [e] at h
      exact h.trans (VR_pre_tb hs ρ S ws P η)

/-- The closure equation behind `VR_close`: closing in the caller's `η` and
then in the variable-free view is closing in `η` (witnesses are closed). -/
theorem cl_CE {η : TEnv} (hc : Coh η) (ρ₀ : Nat → Nat) (P : List Ty) (d : Nat) (ρ ρ' : Nat → Nat)
    (hρ : ∀ k, ρ (k + d) = ρ₀ k) (hρ' : ∀ k, k < d → ρ' k = ρ k) (u : Ty) :
    cl ρ' (TEnv.pre P (CE η)).wit 0 0 (cl ρ₀ η.wit P.length d u) = cl ρ (TEnv.pre P η).wit 0 0 u := by
  have h := cl_comp (ρ := ρ₀) (ρ' := ρ') (W := η.wit) (W' := (TEnv.pre P (CE η)).wit)
    (c := P.length) (d := d) (fun k => (hc k).1) u 0 0
  simp only [Nat.add_zero] at h
  rw [h]
  congr 1
  · funext k
    by_cases hk : k < d
    · simp [hk, hρ' k hk]
    · have e := hρ (k - d)
      rw [Nat.sub_add_cancel (by omega)] at e
      simp [hk, e]
  · funext k
    by_cases hk : k < P.length
    · simp [hk, pre_wit_lt (CE η) η P k hk]
    · simp [hk, pre_wit_ge η P k (by omega)]

/-- **The closing lemma** (T3c).  Under a coherent `η`, `VR`
at `t` (inside `|P|` package binders and `d` index binders, `ρ` agreeing with
`ρ₀` above `d`) is `VR` at its closure, read in the variable-free view with
any valuation `ρ'` that agrees with `ρ` below `d`. -/
theorem VR_close {η : TEnv} (hc : Coh η) (ρ₀ : Nat → Nat) :
    ∀ (t : Ty) (P : List Ty) (d : Nat) (ρ ρ' : Nat → Nat) (S : Shp) (ws : List Word),
      (∀ k, ρ (k + d) = ρ₀ k) → (∀ k, k < d → ρ' k = ρ k) →
      (VR ρ (TEnv.pre P η) t S ws ↔ VR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d t) S ws)
  | .tvar k, P, d, ρ, ρ', S, ws, _, _ => by
      by_cases h : k < P.length
      · simp [cl, h, VR, TEnv.get, pre_rels]
      · have e := (hc (k - P.length)).2.1 ρ' S ws
        simp only [cl, h, ↓reduceIte, VR, TEnv.get, pre_rels]
        rw [VR_pre_tb (hc (k - P.length)).1.1 ρ' S ws P (CE η)]
        constructor
        · rintro ⟨w0, h0, hr⟩; exact VR_up _ _ _ _ h0 (((hc (k - P.length)).2.1 ρ' S w0).1 hr)
        · intro hv; exact ⟨ws, WLe_refl ws, e.2 hv⟩
  | .intS i, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR, ev_clI hρ hρ']
  | .int, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .tid, _, _, _, _, _, _, _, _ => by simp only [cl, VR, pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid, CE_pfr, CE_seen]
  | .fix _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .lanes _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .refine t ψ, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR, pre_ini, CE_ini]
      exact and_congr (VR_close hc ρ₀ t P d ρ ρ' S ws hρ hρ') (by rw [TEnv.selIni_cl (fun k => (hc k).1)]; exact IniR_cl hρ hρ' _ ws ψ)
  | .iex b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun w => and_congr_right fun _ => ?_
      refine VR_close hc ρ₀ b P (d + 1) (vcons w ρ) (vcons w ρ') rb ws (fun k => ?_) (fun k hk => ?_)
      · show vcons w ρ ((k + d) + 1) = ρ₀ k
        rw [vcons_succ]; exact hρ k
      · cases k with
        | zero => rw [vcons_zero, vcons_zero]
        | succ k => rw [vcons_succ, vcons_succ]; exact hρ' k (by omega)
  | .prod a b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR]
      refine exists_congr fun ra => exists_congr fun rb => and_congr_right fun _ =>
        forall_congr' fun n => imp_congr_right fun _ => and_congr_right fun _ => ?_
      exact and_congr (VR_close hc ρ₀ a P d ρ ρ' ra _ hρ hρ') (VR_close hc ρ₀ b P d ρ ρ' rb _ hρ hρ')
  | .sum a b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      have ha : ∀ S ws, VR ρ (TEnv.pre P η) a S ws ↔ VR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d a) S ws :=
        fun S ws => VR_close hc ρ₀ a P d ρ ρ' S ws hρ hρ'
      have hb : ∀ S ws, VR ρ (TEnv.pre P η) b S ws ↔ VR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d b) S ws :=
        fun S ws => VR_close hc ρ₀ b P d ρ ρ' S ws hρ hρ'
      have hau : ∀ S ws, VR ρ (TEnv.pre P η.unsee) a S ws ↔
          VR ρ' (TEnv.pre P (CE η.unsee)) (cl ρ₀ η.wit P.length d a) S ws :=
        fun S ws => VR_close hc.unsee ρ₀ a P d ρ ρ' S ws hρ hρ'
      have hbu : ∀ S ws, VR ρ (TEnv.pre P η.unsee) b S ws ↔
          VR ρ' (TEnv.pre P (CE η.unsee)) (cl ρ₀ η.wit P.length d b) S ws :=
        fun S ws => VR_close hc.unsee ρ₀ b P d ρ ρ' S ws hρ hρ'
      simp only [cl, VR, pre_box, pre_tid, pre_seen, pre_pfr, CE_box, CE_tid, CE_seen, CE_pfr, unsee_pre, CE_unsee, ha, hb, hau, hbu]
  | .code a b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      have hcl := cl_CE hc ρ₀ P d ρ ρ' hρ hρ'
      simp only [cl, VR, hcl, pre_prog, CE_prog]
  | .tex κ b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_close hc ρ₀ b (s :: P) d ρ ρ' rb ws hρ hρ'
  | .unit, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .void, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .array _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .ptr _ _, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid, CE_pfr, CE_seen, ModeOK_clM]
  | .ptrOpt _ _, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid, CE_pfr, CE_seen, ModeOK_clM]
  | .loc _ _, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, pre_ini, pre_rini, CE_sto, CE_tid, CE_pfr, CE_seen, CE_ini, CE_rini, ModeOK_clM, modeIni_clM, modeIni_clM]
  | .share _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .cap _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .word _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .tok _ i, _, _, _, _, _, _, _, _ => by rcases i with _ | ⟨_, _⟩ <;> simp [cl, VR]
  | .word2 _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .epair _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .tokE _ _ _, _, _, _, _, _, _, _, _ => by simp [cl, VR]
  | .mu b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      have hcl := cl_CE hc ρ₀ P d ρ ρ' hρ hρ' (.mu b)
      have e : cl ρ₀ η.wit P.length d (.mu b) = .mu (cl ρ₀ η.wit (P.length + 1) d b) := rfl
      rw [e] at hcl ⊢
      simp only [VR]
      rw [hcl]
      exact VR_close hc ρ₀ b (_ :: P) d ρ ρ' S ws hρ hρ'
  | .iall b, P, d, ρ, ρ', S, ws, hρ, hρ' => by
      simp only [cl, VR]
      refine forall_congr' fun w => ?_
      refine VR_close hc ρ₀ b P (d + 1) (vcons w ρ) (vcons w ρ') S ws (fun k => ?_) (fun k hk => ?_)
      · show vcons w ρ ((k + d) + 1) = ρ₀ k
        rw [vcons_succ]; exact hρ k
      · cases k with
        | zero => rw [vcons_zero, vcons_zero]
        | succ k => rw [vcons_succ, vcons_succ]; exact hρ' k (by omega)

theorem Coh_CE (η : TEnv) : Coh (CE η) := fun _ =>
  ⟨Clo_void, fun _ _ _ => by simp [CE, VR], fun _ _ _ => by simp [CE, TEnv.unsee, VR]⟩

/-- **The transfer lemma** (T3c): when a static signature type closes to a
block's declared type, `VR` at it is `VR` at the declared type in the code
value's own view `CE η`. -/
theorem VR_code {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {σ A : Ty} (h : cl ρ η.wit 0 0 σ = clD A)
    (S : Shp) (ws : List Word) : VR ρ η σ S ws ↔ VR (fun _ => 0) (CE η) A S ws := by
  have h1 := VR_close hc ρ σ [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have h2 := VR_close (Coh_CE η) (fun _ => 0) A [] 0 (fun _ => 0) ρ S ws (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have h3 : VR ρ (CE η) (cl ρ η.wit 0 0 σ) S ws ↔ VR (fun _ => 0) (CE η) A S ws := by
    rw [h]; exact h2.symm
  exact h1.trans h3

/-- A closed type's `VR` in the variable-free view does not depend on `ρ`. -/
theorem VR_clo {η : TEnv} {s : Ty} (hs : Clo s) (ρ ρ' : Nat → Nat) (S : Shp) (ws : List Word) :
    VR ρ (CE η) s S ws ↔ VR ρ' (CE η) s S ws := by
  have h := VR_close (Coh_CE η) ρ s [] 0 ρ ρ' S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  rw [hs.2] at h
  exact h

/-- A coherent variable for the closed witness `s`: `s`'s values. -/
def TEnv.relC (η : TEnv) (s : Ty) : Shp → List Word → Prop :=
  fun S ws => VR (fun _ => 0) (CE η) s S ws

/-- (T3d-2 A1) `relC` with resources. -/
def TEnv.relCR (η : TEnv) (s : Ty) : Shp → List Word → Res → Prop :=
  fun S ws X => VRR (fun _ => 0) (CE η) s S ws X

/-- `unpackT`'s frame: the package's witness as a coherent variable 0. -/
def TEnv.consC (η : TEnv) (s : Ty) : TEnv :=
  η.insR 0 (η.relC s) s (η.unsee.relC s) (η.relCR s) (η.unsee.relCR s)

theorem Coh_consC {η : TEnv} (hc : Coh η) {s : Ty} (hs : Clo s) : Coh (η.consC s) := by
  have e : CE (η.consC s) = CE η := rfl
  intro k
  cases k with
  | zero =>
      have e0 : (η.consC s).wit 0 = s := by simp [TEnv.consC, TEnv.insR]
      have e1 : (η.consC s).rels 0 = η.relC s := by simp [TEnv.consC, TEnv.insR]
      have e2 : (η.consC s).urels 0 = η.unsee.relC s := by simp [TEnv.consC, TEnv.insR]
      have e3 : CE (η.consC s).unsee = CE η.unsee := rfl
      refine ⟨by rw [e0]; exact hs, fun ρ' S ws => ?_, fun ρ' S ws => ?_⟩
      · rw [e, e0, e1]
        simp only [TEnv.relC]
        exact VR_clo hs _ ρ' S ws
      · rw [e3, e0, e2]
        simp only [TEnv.relC]
        exact VR_clo hs _ ρ' S ws
  | succ k =>
      have e0 : (η.consC s).wit (k + 1) = η.wit k := by simp [TEnv.consC, TEnv.insR]
      have e1 : (η.consC s).rels (k + 1) = η.rels k := by simp [TEnv.consC, TEnv.insR]
      have e2 : (η.consC s).urels (k + 1) = η.urels k := by simp [TEnv.consC, TEnv.insR]
      have e3 : CE (η.consC s).unsee = CE η.unsee := rfl
      rw [e, e3, e0, e1, e2]; exact hc k

/-! ### (T3d-2 A1) The structural lemmas for `VRR`

Each mirrors its `VR` counterpart above; `CohR` is `Coh` for the resourceful
relations (kept separate until `VRR` replaces `VR`). -/

theorem VRR_up {ρ : Nat → Nat} {η : TEnv} : ∀ (t : Ty) (rt : Shp) (ws ws' : List Word) (R : Res),
    WLe ws ws' → VRR ρ η t rt ws R → VRR ρ η t rt ws' R := by
  intro t
  induction t generalizing ρ η with
  | tex κ b ih =>
      intro rt ws ws' R e hv
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := hv
      exact ⟨n, rb, s, hr, hs, haf, ih rb ws ws' R e hv⟩
  | prod a b iha ihb =>
      intro rt ws ws' R e hv
      simp only [VRR] at hv ⊢
      obtain ⟨ra, rb, hr, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, hr, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨e.length ▸ h1, iha ra _ _ _ (e.take n) h2, ihb rb _ _ _ (e.drop n) h3⟩
  | iex b ih =>
      intro rt ws ws' R e hv
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := hv
      exact ⟨n, rb, w, hr, ih rb ws ws' R e hv⟩
  | refine t ψ ih =>
      intro rt ws ws' R e hv; simp only [VRR] at hv ⊢; exact ⟨ih rt ws ws' R e hv.1, IniR_vals e.vals ψ hv.2⟩
  | sum a b iha ihb =>
      intro rt ws ws' R e hv
      simp only [VRR] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · exact ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, e.vals.symm.trans hx, ho, hB, hn, hsB,
          hm.imp id (WLe_view e hx B.fr), fun hj => ⟨fun e' => iha _ _ _ _ e ((hA hj).1 e'), (hA hj).2⟩,
          fun hj => ⟨fun e' => ihb _ _ _ _ e ((hA' hj).1 e'), (hA' hj).2⟩⟩⟩
      · obtain ⟨p', hd', ep⟩ := decodeArm_wle e hd
        refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p', hd', fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', iha _ _ _ _ eq hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj
          obtain ⟨q', hq', eq⟩ := ofArm_wle ep hq
          exact ⟨q', hq', ihb _ _ _ _ eq hv⟩
  | mu b ih => intro rt ws ws' R e hv; simp only [VRR] at hv ⊢; exact ih rt ws ws' R e hv
  | iall b ih => intro rt ws ws' R e hv; simp only [VRR] at hv ⊢; exact fun n => ih rt ws ws' R e (hv n)
  | tvar k =>
      intro rt ws ws' R e hv; simp only [VRR] at hv ⊢
      obtain ⟨w0, h0, hr⟩ := hv
      exact ⟨w0, WLe_trans h0 e, hr⟩
  | ptr μ u =>
      intro rt ws ws' R e hv; simp only [VRR] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      exact ⟨⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
        ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩, hR.trans (ownW_vals e.vals)⟩
  | ptrOpt μ u =>
      intro rt ws ws' R e hv; simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl (e.vals.symm.trans hn), hR.trans (ownW_vals e.vals)⟩
      · exact ⟨Or.inr ⟨a, c, e.vals.symm.trans h1, h2, h3, h4,
          ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩, hR.trans (ownW_vals e.vals)⟩
  | loc μ u =>
      intro rt ws ws' R e hv; simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl ⟨e.vals.symm.trans hn.1, hn.2⟩, hR.trans (ownW_vals e.vals)⟩
      · exact ⟨Or.inr ⟨a, c, U, e.vals.symm.trans h1, h3, h4, hF,
          ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5, h6⟩, hR.trans (ownW_vals e.vals)⟩
  | tid =>
      intro rt ws ws' R e hv; simp only [VRR, VR] at hv ⊢
      obtain ⟨⟨l, c, h1, h2, h3, h5⟩, hR⟩ := hv
      exact ⟨⟨l, c, e.vals.symm.trans h1, h2, h3,
        ModeOK_mono (fun _ _ x => x) (fun _ x => x) (WLe_view e h1) h5⟩, hR⟩
  | _ => intro rt ws ws' R e hv; simp only [VRR] at hv ⊢ <;> first | exact hv | (rw [← e.vals]; exact hv)


theorem VRR_shift (η : TEnv) : ∀ (t : Ty) (c w : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (R : Res),
    VRR (vins c w ρ) η (t.shiftI c) rt ws R ↔ VRR ρ η t rt ws R
  | .intS i, c, w, ρ, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .int, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .tid, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, VR]
  | .fix _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .lanes _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .refine t ψ, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR]; exact and_congr (VRR_shift η t c w ρ rt ws R) (by rw [TEnv.selIni_shiftI]; exact IniR_shift c w ρ _ ws ψ)
  | .iex b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR]
      constructor
      · rintro ⟨n, rb, v, hr, hv⟩
        rw [← vins_succ] at hv
        exact ⟨n, rb, v, hr, (VRR_shift η b (c + 1) w (vcons v ρ) rb ws R).1 hv⟩
      · rintro ⟨n, rb, v, hr, hv⟩
        refine ⟨n, rb, v, hr, ?_⟩
        rw [← vins_succ]
        exact (VRR_shift η b (c + 1) w (vcons v ρ) rb ws R).2 hv
  | .prod a b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR, VRR_shift η a c w ρ, VRR_shift η b c w ρ]
  | .unit, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .void, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .sum a b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR, VRR_shift η a c w ρ, VRR_shift η b c w ρ, VRR_shift η.unsee a c w ρ,
        VRR_shift η.unsee b c w ρ]
  | .code a b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR, cl_vins]
  | .array _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .ptr _ _, _, _, _, _, _, _ => by simp only [Ty.shiftI, VRR, cl_vins, ModeOK_shift, ownW_shift]
  | .ptrOpt _ _, _, _, _, _, _, _ => by simp only [Ty.shiftI, VRR, cl_vins, ModeOK_shift, ownW_shift]
  | .loc _ _, _, _, _, _, _, _ => by simp only [Ty.shiftI, VRR, cl_vins, ModeOK_shift, modeIni_shift, ownW_shift]
  | .share _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .cap _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .word _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .tok _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .word2 _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .tok2 _ _ _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .epair _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .tokE _ _ _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR, ev_shift]
  | .tvar _, _, _, _, _, _, _ => by simp [Ty.shiftI, VRR]
  | .mu b, c, w, ρ, rt, ws, R => by
      have e := cl_vins c w ρ η.wit (.mu b)
      simp only [Ty.shiftI] at e
      simp only [Ty.shiftI, VRR, e]
      exact VRR_shift _ b c w ρ rt ws R
  | .iall b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR]
      refine forall_congr' fun n => ?_
      rw [← vins_succ]
      exact VRR_shift η b (c + 1) w (vcons n ρ) rt ws R
  | .tex κ b, c, w, ρ, rt, ws, R => by
      simp only [Ty.shiftI, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VRR_shift (η.push0 s) b c w ρ rb ws R


theorem VRR_instT (w : Idx) (η : TEnv) :
    ∀ (t : Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (R : Res),
      VRR ρ η (instT [w] d t) rt ws R ↔ VRR (vins d (ev (fun k => ρ (k + d)) w) ρ) η t rt ws R
  | .intS i, d, ρ, _, _, _ => by simp [instT, VRR, ev_instI]
  | .int, _, _, _, _, _ => by simp [instT, VRR]
  | .tid, _, _, _, _, _ => by simp [instT, VRR, VR]
  | .fix _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .lanes _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .refine t ψ, d, ρ, rt, ws, R => by
      simp only [instT, VRR]; exact and_congr (VRR_instT w η t d ρ rt ws R) (by rw [TEnv.selIni_instT]; exact IniR_inst w d ρ _ ws ψ)
  | .iex b, d, ρ, rt, ws, R => by
      have e : ∀ v, vins (d + 1) (ev (fun k => vcons v ρ (k + (d + 1))) w) (vcons v ρ) =
          vcons v (vins d (ev (fun k => ρ (k + d)) w) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vins_succ]
      simp only [instT, VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      rw [VRR_instT w η b (d + 1) (vcons v ρ) rb ws R, e v]
  | .prod a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, VRR_instT w η a d ρ, VRR_instT w η b d ρ]
  | .unit, _, _, _, _, _ => by simp [instT, VRR]
  | .void, _, _, _, _, _ => by simp [instT, VRR]
  | .sum a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, VRR_instT w η a d ρ, VRR_instT w η b d ρ, VRR_instT w η.unsee a d ρ,
        VRR_instT w η.unsee b d ρ]
  | .code a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, cl_inst1]
  | .array _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .ptr _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_inst1, ModeOK_inst, ownW_inst]
  | .ptrOpt _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_inst1, ModeOK_inst, ownW_inst]
  | .loc _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_inst1, ModeOK_inst, modeIni_inst, ownW_inst]
  | .share _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .cap _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .word _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .tok _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .word2 _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .tok2 _ _ _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .epair _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .tokE _ _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instI]
  | .tvar _, _, _, _, _, _ => by simp [instT, VRR]
  | .mu b, d, ρ, rt, ws, R => by
      have e := cl_inst1 w d ρ η.wit (.mu b)
      simp only [instT] at e
      simp only [instT, VRR, e]
      exact VRR_instT w _ b d ρ rt ws R
  | .iall b, d, ρ, rt, ws, R => by
      have e : ∀ v, vins (d + 1) (ev (fun k => vcons v ρ (k + (d + 1))) w) (vcons v ρ) =
          vcons v (vins d (ev (fun k => ρ (k + d)) w) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vins_succ]
      simp only [instT, VRR]
      refine forall_congr' fun v => ?_
      rw [VRR_instT w η b (d + 1) (vcons v ρ) rt ws R, e v]
  | .tex κ b, d, ρ, rt, ws, R => by
      simp only [instT, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VRR_instT w (η.push0 s) b d ρ rb ws R

abbrev RRel := Shp → List Word → Res → Prop

theorem VRR_shiftTU : ∀ (t : Ty) (c : Nat) (η : TEnv) (R : Shp → List Word → Prop) (s : Ty)
    (UR : Shp → List Word → Prop) (RR URR : RRel)
    (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res),
    VRR ρ (η.insR c R s UR RR URR) (t.shiftT c) rt ws X ↔ VRR ρ η t rt ws X
  | .tvar k, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      by_cases h : k ≥ c
      · have h1 : ¬ k + 1 < c := by omega
        have h2 : k + 1 ≠ c := by omega
        simp [Ty.shiftT, h, VRR, TEnv.insR, h1, h2]
      · have h1 : k < c := by omega
        simp [Ty.shiftT, h, VRR, TEnv.insR, h1]
  | .intS i, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .int, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .tid, _, _, _, _, _, _, _, _, _, _, _ => by simp only [Ty.shiftT, VRR, VR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen]
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .refine t ψ, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR, TEnv.insR_ini]; exact and_congr (VRR_shiftTU t c η R s UR RR URR ρ rt ws X) (by rw [TEnv.selIni_shiftT_insR])
  | .iex b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun v => and_congr_right fun _ =>
        VRR_shiftTU b c η R s UR RR URR (vcons v ρ) rb ws X
  | .prod a b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR, VRR_shiftTU a c η R s UR RR URR ρ, VRR_shiftTU b c η R s UR RR URR ρ]
  | .sum a b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR, VRR_shiftTU a c η R s UR RR URR ρ, VRR_shiftTU b c η R s UR RR URR ρ, unsee_insR,
        VRR_shiftTU a c η.unsee UR s UR URR URR ρ, VRR_shiftTU b c η.unsee UR s UR URR URR ρ, TEnv.insR_box,
        TEnv.insR_tid, TEnv.insR_seen, TEnv.insR_pfr]
  | .code a b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR, cl_insR, TEnv.insR_prog]
  | .tex κ b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun s' => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [← insR_push0 (UR := UR) (RR := RR) (URR := URR)]
      exact VRR_shiftTU b (c + 1) (η.push0 s') R s UR RR URR ρ rb ws X
  | .unit, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .void, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .ptr _ _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VRR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen]
  | .ptrOpt _ _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VRR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen]
  | .loc _ _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.shiftT, VRR, cl_insR, TEnv.insR_sto, TEnv.insR_tid, TEnv.insR_pfr, TEnv.insR_seen, TEnv.insR_ini, TEnv.insR_rini]
  | .share _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp [Ty.shiftT, VRR]
  | .mu b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      have e := cl_insR c R s η ρ (.mu b) UR RR URR
      simp only [Ty.shiftT] at e
      simp only [Ty.shiftT, VRR, e]
      rw [← insR_push0 (UR := UR) (RR := RR) (URR := URR)]
      exact VRR_shiftTU b (c + 1) _ R s UR RR URR ρ rt ws X
  | .iall b, c, η, R, s, UR, RR, URR, ρ, rt, ws, X => by
      simp only [Ty.shiftT, VRR]
      exact forall_congr' fun v => VRR_shiftTU b c η R s UR RR URR (vcons v ρ) rt ws X

theorem VRR_shiftTN (σ : Ty) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res) : ∀ (P : List Ty) (η : TEnv),
    VRR ρ (TEnv.pre P η) (shiftTN P.length σ) rt ws X ↔ VRR ρ η σ rt ws X
  | [], _ => Iff.rfl
  | s :: P, η => by
      show VRR ρ ((TEnv.pre P η).insR 0 (fun _ _ => False) s) (Ty.shiftT 0 (shiftTN P.length σ)) rt ws X ↔ _
      rw [VRR_shiftTU]; exact VRR_shiftTN σ ρ rt ws X P η


theorem push0_rrs_mono {η₁ η₂ : TEnv} {s s' : Ty} (hr : ∀ k S vs X, η₁.rrs k S vs X → η₂.rrs k S vs X) :
    ∀ k S vs X, (η₁.push0 s).rrs k S vs X → (η₂.push0 s').rrs k S vs X
  | 0, _, _, _, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | k + 1, S, vs, X, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢; exact hr k S vs X h
theorem push0_urrs_mono {η₁ η₂ : TEnv} {s s' : Ty} (hr : ∀ k S vs X, η₁.urrs k S vs X → η₂.urrs k S vs X) :
    ∀ k S vs X, (η₁.push0 s).urrs k S vs X → (η₂.push0 s').urrs k S vs X
  | 0, _, _, _, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | k + 1, S, vs, X, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢; exact hr k S vs X h

theorem VRR_mono : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res),
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S vs Y) → (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S vs Y) →
    η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    η₁.tid = η₂.tid → (∀ l c, η₁.sto l = some c → η₂.sto l = some c) →
    (∀ l, η₁.ini l ≤ η₂.ini l) → (∀ l f, η₁.pfr l = some f → η₂.pfr l = some f) →
    (∀ l, η₁.seen l → η₂.seen l) → (∀ l B, η₁.box l = some B → η₂.box l = some B) →
    VRR ρ η₁ t rt ws X → (hri : ∀ l, η₁.rini l ≤ η₂.rini l := by rini_le) → VRR ρ η₂ t rt ws X
  | .tvar k, η₁, η₂, ρ, rt, ws, X, hr, hur, _, _, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨w0, h0, h1⟩ := hv; exact ⟨w0, h0, hr k rt _ X h1⟩
  | .refine t ψ, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢; exact ⟨VRR_mono t η₁ η₂ ρ rt ws X hr hur hw hp ht hs hi hP hS hBx hv.1, IniR_mono (TEnv.selIni_le hw hi hri t) hv.2⟩
  | .iex b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VRR_mono b η₁ η₂ (vcons w ρ) rb ws X hr hur hw hp ht hs hi hP hS hBx h2⟩
  | .prod a b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨ra, rb, h1, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, h1, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn
      exact ⟨e1, VRR_mono a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx e2,
        VRR_mono b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx e3⟩
  | .sum a b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h2, h3⟩⟩ := hv
      · refine ⟨n, Ra, Rb, h1, Or.inl ⟨hb, x, s, B, hx, ho, hBx _ _ hB, hn, hsB, hm.imp (fun ⟨h1, f, h2, h3⟩ => ⟨hS _ h1, f, hP _ _ h2, h3⟩) id,
          fun hj => ⟨fun e => VRR_mono a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => VRR_mono b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_mono a η₁.unsee η₂.unsee ρ _ _ _ hur hur hw hp ht hs hi hP
            (fun _ h => h.elim) hBx hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, VRR_mono b η₁.unsee η₂.unsee ρ _ _ _ hur hur hw hp ht hs hi hP
            (fun _ h => h.elim) hBx hv⟩
      · refine ⟨n, Ra, Rb, h1, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VRR_mono a η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
        · obtain ⟨q, hq, hv⟩ := h3 hj; exact ⟨q, hq, VRR_mono b η₁ η₂ ρ _ _ _ hr hur hw hp ht hs hi hP hS hBx hv⟩
  | .code a b, η₁, η₂, ρ, rt, ws, X, _, _, hw, hp, _, _, _, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VRR_mono b (η₁.push0 s) (η₂.push0 s) ρ rb ws X
        (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp ht hs hi hP hS hBx h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .ptr μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      exact ⟨⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5, h6⟩, hR⟩
  | .ptrOpt μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, _, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl hn, hR⟩
      · exact ⟨Or.inr ⟨a, c, h1, h2, hs _ _ h3, hw ▸ h4, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5, h6⟩, hR⟩
  | .loc μ u, η₁, η₂, ρ, rt, ws, X, _, _, hw, _, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      obtain ⟨hn | ⟨a, c, U, h1, h3, h4, hF, h5, h6⟩, hR⟩ := hv
      · exact ⟨Or.inl ⟨hn.1, hw ▸ hn.2⟩, hR⟩
      · exact ⟨Or.inr ⟨a, c, U, h1, hs _ _ h3, h4, hw ▸ hF, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5,
          IniAt_mono (modeIni_le hi hri μ) h6⟩, hR⟩
  | .mu b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      rw [← hw]
      refine VRR_mono b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b))) ρ rt ws X
        (push0_rrs_mono hr) (push0_urrs_mono hur) ?_ hp ht hs hi hP hS hBx hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, η₁, η₂, ρ, rt, ws, X, hr, hur, hw, hp, ht, hs, hi, hP, hS, hBx, hv, hri => by
      simp only [VRR] at hv ⊢
      exact fun n => VRR_mono b η₁ η₂ (vcons n ρ) rt ws X hr hur hw hp ht hs hi hP hS hBx (hv n)
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tid, _, _, _, _, _, _, _, _, _, _, ht, hs, _, hP, hS, _, hv, _ => by
        simp only [VRR, VR] at hv ⊢
        obtain ⟨⟨l, c, h1, h2, h3, h5⟩, hR⟩ := hv
        exact ⟨⟨l, c, h1, hs _ _ h2, h3, ht ▸ ModeOK_mono hP hS (fun _ x => x) h5⟩, hR⟩
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simp [VRR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hri => by simpa only [VRR] using hv


/-- (T3d-2 A1) Coherence of the resourceful relations: variable `k` denotes,
with resources, exactly its witness's values in `CE η`.  Kept beside `Coh`
while `VR` migrates to `VRR`; folded into `Coh` at the end. -/
def CohR (η : TEnv) : Prop :=
  ∀ k, (∀ (ρ' : Nat → Nat) (S : Shp) (ws : List Word) (X : Res),
    η.rrs k S ws X ↔ VRR ρ' (CE η) (η.wit k) S ws X) ∧ ∀ (ρ' : Nat → Nat) (S : Shp) (ws : List Word) (X : Res),
    η.urrs k S ws X ↔ VRR ρ' (CE η.unsee) (η.wit k) S ws X

theorem CohR.unsee {η : TEnv} (hr : CohR η) : CohR η.unsee := fun k => ⟨(hr k).2, (hr k).2⟩

theorem VRR_pre_tb {s : Ty} (hs : tb 0 s = true) (ρ : Nat → Nat) (S : Shp) (ws : List Word) (X : Res) :
    ∀ (P : List Ty) (η : TEnv), VRR ρ (TEnv.pre P η) s S ws X ↔ VRR ρ η s S ws X
  | [], _ => Iff.rfl
  | s' :: P, η => by
      have e : s.shiftT 0 = s := tb_shiftT s hs (Nat.le_refl 0)
      have h := VRR_shiftTU s 0 (TEnv.pre P η) (fun _ _ => False) s' (fun _ _ => False)
        (fun _ _ _ => False) (fun _ _ _ => False) ρ S ws X
      rw [e] at h
      exact h.trans (VRR_pre_tb hs ρ S ws X P η)

theorem VRR_close {η : TEnv} (hc : Coh η) (hr : CohR η) (ρ₀ : Nat → Nat) :
    ∀ (t : Ty) (P : List Ty) (d : Nat) (ρ ρ' : Nat → Nat) (S : Shp) (ws : List Word) (X : Res),
      (∀ k, ρ (k + d) = ρ₀ k) → (∀ k, k < d → ρ' k = ρ k) →
      (VRR ρ (TEnv.pre P η) t S ws X ↔ VRR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d t) S ws X)
  | .tvar k, P, d, ρ, ρ', S, ws, X, _, _ => by
      by_cases h : k < P.length
      · simp [cl, h, VRR, pre_rrs]
      · have e := (hr (k - P.length)).1 ρ' S ws X
        simp only [cl, h, ↓reduceIte, VRR, pre_rrs]
        rw [VRR_pre_tb (hc (k - P.length)).1.1 ρ' S ws X P (CE η)]
        constructor
        · rintro ⟨w0, h0, hx⟩; exact VRR_up _ _ _ _ _ h0 (((hr (k - P.length)).1 ρ' S w0 X).1 hx)
        · intro hv; exact ⟨ws, WLe_refl ws, e.2 hv⟩
  | .intS i, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR, ev_clI hρ hρ']
  | .int, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .tid, _, _, _, _, _, _, _, _, _ => by simp only [cl, VRR, VR, pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid, CE_pfr, CE_seen]
  | .fix _ _, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .lanes _ _, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .refine t ψ, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR, pre_ini, CE_ini]
      exact and_congr (VRR_close hc hr ρ₀ t P d ρ ρ' S ws X hρ hρ') (by rw [TEnv.selIni_cl (fun k => (hc k).1)]; exact IniR_cl hρ hρ' _ ws ψ)
  | .iex b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun w => and_congr_right fun _ => ?_
      refine VRR_close hc hr ρ₀ b P (d + 1) (vcons w ρ) (vcons w ρ') rb ws X (fun k => ?_) (fun k hk => ?_)
      · show vcons w ρ ((k + d) + 1) = ρ₀ k
        rw [vcons_succ]; exact hρ k
      · cases k with
        | zero => rw [vcons_zero, vcons_zero]
        | succ k => rw [vcons_succ, vcons_succ]; exact hρ' k (by omega)
  | .prod a b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR]
      refine exists_congr fun ra => exists_congr fun rb => and_congr_right fun _ =>
        exists_congr fun Ra => exists_congr fun Rb => and_congr_right fun _ => and_congr_right fun _ =>
        forall_congr' fun n => imp_congr_right fun _ => and_congr_right fun _ => ?_
      exact and_congr (VRR_close hc hr ρ₀ a P d ρ ρ' ra _ _ hρ hρ') (VRR_close hc hr ρ₀ b P d ρ ρ' rb _ _ hρ hρ')
  | .sum a b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      have ha : ∀ S ws X, VRR ρ (TEnv.pre P η) a S ws X ↔
          VRR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d a) S ws X :=
        fun S ws X => VRR_close hc hr ρ₀ a P d ρ ρ' S ws X hρ hρ'
      have hb : ∀ S ws X, VRR ρ (TEnv.pre P η) b S ws X ↔
          VRR ρ' (TEnv.pre P (CE η)) (cl ρ₀ η.wit P.length d b) S ws X :=
        fun S ws X => VRR_close hc hr ρ₀ b P d ρ ρ' S ws X hρ hρ'
      have hau : ∀ S ws X, VRR ρ (TEnv.pre P η.unsee) a S ws X ↔
          VRR ρ' (TEnv.pre P (CE η.unsee)) (cl ρ₀ η.wit P.length d a) S ws X :=
        fun S ws X => VRR_close hc.unsee hr.unsee ρ₀ a P d ρ ρ' S ws X hρ hρ'
      have hbu : ∀ S ws X, VRR ρ (TEnv.pre P η.unsee) b S ws X ↔
          VRR ρ' (TEnv.pre P (CE η.unsee)) (cl ρ₀ η.wit P.length d b) S ws X :=
        fun S ws X => VRR_close hc.unsee hr.unsee ρ₀ b P d ρ ρ' S ws X hρ hρ'
      simp only [cl, VRR, pre_box, pre_tid, pre_seen, pre_pfr, CE_box, CE_tid, CE_seen, CE_pfr, unsee_pre, CE_unsee, ha, hb, hau, hbu]
  | .code a b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      have hcl := cl_CE hc ρ₀ P d ρ ρ' hρ hρ'
      simp only [cl, VRR, hcl, pre_prog, CE_prog]
  | .tex κ b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VRR_close hc hr ρ₀ b (s :: P) d ρ ρ' rb ws X hρ hρ'
  | .unit, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .void, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .array _ _, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .ptr _ _, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid,
        CE_pfr, CE_seen, ModeOK_clM, ownW_clM]
  | .ptrOpt _ _, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, CE_sto, CE_tid,
        CE_pfr, CE_seen, ModeOK_clM, ownW_clM]
  | .loc _ _, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR, cl_CE hc ρ₀ P d ρ ρ' hρ hρ', pre_sto, pre_tid, pre_pfr, pre_seen, pre_ini, pre_rini, CE_sto,
        CE_tid, CE_pfr, CE_seen, CE_ini, CE_rini, ModeOK_clM, modeIni_clM, ownW_clM]
  | .share _, _, _, _, _, _, _, _, hρ, hρ' => by simp [cl, VRR, ev_clI hρ hρ']
  | .cap _ _, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .word _ _, _, _, _, _, _, _, _, hρ, hρ' => by simp [cl, VRR, ev_clI hρ hρ']
  | .tok _ i, _, _, _, _, _, _, _, hρ, hρ' => by rcases i with _ | ⟨_, _⟩ <;> simp [cl, VRR, ev_clI hρ hρ']
  | .word2 _ _, _, _, _, _, _, _, _, hρ, hρ' => by simp [cl, VRR, ev_clI hρ hρ']
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, hρ, hρ' => by simp [cl, VRR, ev_clI hρ hρ']
  | .epair _ _, _, _, _, _, _, _, _, _, _ => by simp [cl, VRR]
  | .tokE _ _ _, _, _, _, _, _, _, _, hρ, hρ' => by simp [cl, VRR, ev_clI hρ hρ']
  | .mu b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      have hcl := cl_CE hc ρ₀ P d ρ ρ' hρ hρ' (.mu b)
      have e : cl ρ₀ η.wit P.length d (.mu b) = .mu (cl ρ₀ η.wit (P.length + 1) d b) := rfl
      rw [e] at hcl ⊢
      simp only [VRR]
      rw [hcl]
      exact VRR_close hc hr ρ₀ b (_ :: P) d ρ ρ' S ws X hρ hρ'
  | .iall b, P, d, ρ, ρ', S, ws, X, hρ, hρ' => by
      simp only [cl, VRR]
      refine forall_congr' fun w => ?_
      refine VRR_close hc hr ρ₀ b P (d + 1) (vcons w ρ) (vcons w ρ') S ws X (fun k => ?_) (fun k hk => ?_)
      · show vcons w ρ ((k + d) + 1) = ρ₀ k
        rw [vcons_succ]; exact hρ k
      · cases k with
        | zero => rw [vcons_zero, vcons_zero]
        | succ k => rw [vcons_succ, vcons_succ]; exact hρ' k (by omega)

theorem CohR_CE (η : TEnv) : CohR (CE η) := fun _ =>
  ⟨fun _ _ _ _ => by simp [CE, VRR], fun _ _ _ _ => by simp [CE, TEnv.unsee, VRR]⟩

theorem VRR_code {η : TEnv} (hc : Coh η) (hr : CohR η) {ρ : Nat → Nat} {σ A : Ty} (h : cl ρ η.wit 0 0 σ = clD A)
    (S : Shp) (ws : List Word) (X : Res) : VRR ρ η σ S ws X ↔ VRR (fun _ => 0) (CE η) A S ws X := by
  have h1 := VRR_close hc hr ρ σ [] 0 ρ ρ S ws X (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have h2 := VRR_close (Coh_CE η) (CohR_CE η) (fun _ => 0) A [] 0 (fun _ => 0) ρ S ws X (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have h3 : VRR ρ (CE η) (cl ρ η.wit 0 0 σ) S ws X ↔ VRR (fun _ => 0) (CE η) A S ws X := by
    rw [h]; exact h2.symm
  exact h1.trans h3

theorem VRR_clo {η : TEnv} {s : Ty} (hs : Clo s) (ρ ρ' : Nat → Nat) (S : Shp) (ws : List Word) (X : Res) :
    VRR ρ (CE η) s S ws X ↔ VRR ρ' (CE η) s S ws X := by
  have h := VRR_close (Coh_CE η) (CohR_CE η) ρ s [] 0 ρ ρ' S ws X (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  rw [hs.2] at h
  exact h


theorem CohR_consC {η : TEnv} (hr : CohR η) {s : Ty} (hs : Clo s) : CohR (η.consC s) := by
  have e : CE (η.consC s) = CE η := rfl
  intro k
  cases k with
  | zero =>
      have e0 : (η.consC s).wit 0 = s := by simp [TEnv.consC, TEnv.insR]
      have e1 : (η.consC s).rrs 0 = η.relCR s := by simp [TEnv.consC, TEnv.insR]
      have e2 : (η.consC s).urrs 0 = η.unsee.relCR s := by simp [TEnv.consC, TEnv.insR]
      have e3 : CE (η.consC s).unsee = CE η.unsee := rfl
      refine ⟨fun ρ' S ws X => ?_, fun ρ' S ws X => ?_⟩
      · rw [e, e0, e1]; simp only [TEnv.relCR]; exact VRR_clo hs _ ρ' S ws X
      · rw [e3, e0, e2]; simp only [TEnv.relCR]; exact VRR_clo hs _ ρ' S ws X
  | succ k =>
      have e0 : (η.consC s).wit (k + 1) = η.wit k := by simp [TEnv.consC, TEnv.insR]
      have e1 : (η.consC s).rrs (k + 1) = η.rrs k := by simp [TEnv.consC, TEnv.insR]
      have e2 : (η.consC s).urrs (k + 1) = η.urrs k := by simp [TEnv.consC, TEnv.insR]
      have e3 : CE (η.consC s).unsee = CE η.unsee := rfl
      rw [e, e3, e0, e1, e2]; exact hr k

/-- Coherent views link their resourceful relations to the plain ones. -/
theorem RLink_of {η : TEnv} (hc : Coh η) (hr : CohR η) : RLink η :=
  ⟨fun k S ws X h => ((hc k).2.1 (fun _ => 0) S ws).2
      (VRR_VR _ ⟨fun _ _ _ _ h => by simp [CE] at h, fun _ _ _ _ h => by simp [CE] at h⟩
        (((hr k).1 (fun _ => 0) S ws X).1 h)),
   fun k S ws X h => ((hc k).2.2 (fun _ => 0) S ws).2
      (VRR_VR _ ⟨fun _ _ _ _ h => by simp [CE, TEnv.unsee] at h, fun _ _ _ _ h => by simp [CE, TEnv.unsee] at h⟩
        (((hr k).2 (fun _ => 0) S ws X).1 h))⟩

/-- (T3d-2 A1 P3) **Copyable values carry nothing.**  A type that is not
affine, read where every copy-kinded variable denotes resource-free values,
has only resource-free values. -/
theorem VRR_copy_zero : ∀ (t : Ty) (ke : KEnv) (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word) (X : Res),
    Ty.affineIn ke t = false →
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.rrs k S vs Y → Y = .zero) →
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.urrs k S vs Y → Y = .zero) →
    VRR ρ η t rt ws X → X = .zero
  | .tvar k, ke, ρ, η, rt, ws, X, ha, hr, _, hv => by
      simp only [Ty.affineIn, Bool.not_eq_false'] at ha
      simp only [VRR] at hv
      obtain ⟨w0, -, h⟩ := hv
      exact hr k ha rt w0 X h
  | .refine t _, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [VRR] at hv
      exact VRR_copy_zero t ke ρ η rt ws X ha hr hu hv.1
  | .iex b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [VRR] at hv
      obtain ⟨_, rb, w, -, hv⟩ := hv
      exact VRR_copy_zero b ke _ η rb ws X ha hr hu hv
  | .iall b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [VRR] at hv
      exact VRR_copy_zero b ke _ η rt ws X ha hr hu (hv 0)
  | .prod a b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at ha; simp only [VRR] at hv
      obtain ⟨ra, rb, -, Ra, Rb, hR, hz, hf⟩ := hv
      cases hn : ra.wc with
      | none => exact hz hn
      | some n =>
          obtain ⟨-, h1, h2⟩ := hf n hn
          rw [hR, VRR_copy_zero a ke ρ η ra _ Ra ha.1 hr hu h1, VRR_copy_zero b ke ρ η rb _ Rb ha.2 hr hu h2]
          exact Res.zero_add _
  | .sum a b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn, Bool.or_eq_false_iff] at ha; simp only [VRR] at hv
      obtain ⟨n, Ra, Rb, -, ⟨-, x, s, B, -, -, -, -, -, -, hA, hA'⟩ | ⟨j, p, -, h1, h2⟩⟩ := hv
      · by_cases hj : B.tag - s < (armsOf Ra).length
        · cases hb : isBoxed Ra with
          | true => exact VRR_copy_zero a ke ρ η _ ws X ha.1 hr hu ((hA hj).1 hb)
          | false =>
              obtain ⟨q, -, -, -, -, hq⟩ := (hA hj).2 hb
              exact VRR_copy_zero a ke ρ η.unsee _ q X ha.1 hu hu hq
        · have hj' : (armsOf Ra).length ≤ B.tag - s := by omega
          cases hb : isBoxed Rb with
          | true => exact VRR_copy_zero b ke ρ η _ ws X ha.2 hr hu ((hA' hj').1 hb)
          | false =>
              obtain ⟨q, -, -, -, -, hq⟩ := (hA' hj').2 hb
              exact VRR_copy_zero b ke ρ η.unsee _ q X ha.2 hu hu hq
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, hq⟩ := h1 hj; exact VRR_copy_zero a ke ρ η _ q X ha.1 hr hu hq
        · obtain ⟨q, -, hq⟩ := h2 (by omega); exact VRR_copy_zero b ke ρ η _ q X ha.2 hr hu hq
  | .tex κ b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [VRR] at hv
      obtain ⟨_, rb, s, -, -, -, hv⟩ := hv
      refine VRR_copy_zero b (some κ :: ke) ρ (η.push0 s) rb ws X ha (fun k hk S vs Y h => ?_)
        (fun k hk S vs Y h => ?_) hv
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
            exact hr k (by simpa [KEnv.ask] using hk) S vs Y h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
            exact hu k (by simpa [KEnv.ask] using hk) S vs Y h
  | .mu b, ke, ρ, η, rt, ws, X, ha, hr, hu, hv => by
      simp only [Ty.affineIn] at ha; simp only [VRR] at hv
      refine VRR_copy_zero b (none :: ke) ρ _ rt ws X ha (fun k hk S vs Y h => ?_) (fun k hk S vs Y h => ?_) hv
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
            exact hr k (by simpa [KEnv.ask] using hk) S vs Y h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
            exact hu k (by simpa [KEnv.ask] using hk) S vs Y h
  | .array _ _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .unit, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .cap _ _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .void, _, _, _, _, _, _, _, _, _, hv => by simp [VRR] at hv
  | .intS _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .int, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .tid, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .fix _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .lanes _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .code _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .ptr μ _, _, _, _, _, _, _, ha, _, _, hv => by
      simp only [VRR] at hv; rw [hv.2]; cases μ <;> simp_all [Ty.affineIn]
  | .ptrOpt μ _, _, _, _, _, _, _, ha, _, _, hv => by
      simp only [VRR] at hv; rw [hv.2]; cases μ <;> simp_all [Ty.affineIn]
  | .loc μ _, _, _, _, _, _, _, ha, _, _, hv => by
      simp only [VRR] at hv; rw [hv.2]; cases μ <;> simp_all [Ty.affineIn]
  | .tok _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .tok2 _ _ _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .tokE _ _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .share _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .word _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .word2 _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha
  | .epair _ _, _, _, _, _, _, _, ha, _, _, _ => by simp [Ty.affineIn] at ha

/-! ### T3c-4b: Σ grows under a frame

Σ belongs to the thread, not to a frame: a callee's allocation must be visible
to its callers when it returns.  `Ext η η'`: `η'` is a coherent view with the
same witnesses, program and thread and a larger Σ.  `VR` is monotone along it
(`VR_ext`), and two coherent views that agree on witnesses and `CE` have the
same `VR` (`VR_coh`). -/

def Ext (η η' : TEnv) : Prop :=
  Coh η' ∧ η'.wit = η.wit ∧ η'.prog = η.prog ∧ η'.tid = η.tid ∧
    (∀ l c, η.sto l = some c → η'.sto l = some c) ∧ (∀ l, η.ini l ≤ η'.ini l) ∧
    (∀ l f, η.pfr l = some f → η'.pfr l = some f) ∧ (∀ l, η.seen l → η'.seen l) ∧
    (∀ l B, η.box l = some B → η'.box l = some B) ∧ η.rid ≤ η'.rid ∧ CohR η' ∧
    (∀ l, η.rini l ≤ η'.rini l)

theorem Ext.rini {η η' : TEnv} (h : Ext η η') : ∀ l, η.rini l ≤ η'.rini l := h.2.2.2.2.2.2.2.2.2.2.2

theorem Ext_refl {η : TEnv} (hc : Coh η) (hr : CohR η) : Ext η η :=
  ⟨hc, rfl, rfl, rfl, fun _ _ h => h, fun _ => Nat.le_refl _, fun _ _ h => h, fun _ h => h, fun _ _ h => h, Nat.le_refl _,
    hr, fun _ => Nat.le_refl _⟩

theorem Ext_trans {η₁ η₂ η₃ : TEnv} (a : Ext η₁ η₂) (b : Ext η₂ η₃) : Ext η₁ η₃ :=
  ⟨b.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
    fun l c h => b.2.2.2.2.1 l c (a.2.2.2.2.1 l c h), fun l => Nat.le_trans (a.2.2.2.2.2.1 l) (b.2.2.2.2.2.1 l),
    fun l f h => b.2.2.2.2.2.2.1 l f (a.2.2.2.2.2.2.1 l f h), fun l h => b.2.2.2.2.2.2.2.1 l (a.2.2.2.2.2.2.2.1 l h),
    fun l B h => b.2.2.2.2.2.2.2.2.1 l B (a.2.2.2.2.2.2.2.2.1 l B h),
    Nat.le_trans a.2.2.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.2.1,
    fun l => Nat.le_trans (a.rini l) (b.rini l)⟩

/-- `η` at another Σ (and initialised counts, frontiers, seen set), with its
relations re-read there. -/
def TEnv.withSto (η : TEnv) (s : WeakMem.AllocLabel → Option Cell) (i : WeakMem.AllocLabel → Nat := η.ini)
    (P : WeakMem.AllocLabel → Option WeakMem.Ts := η.pfr) (S : WeakMem.AllocLabel → Prop := η.seen)
    (Bx : WeakMem.AllocLabel → Option Box := η.box) (Rd : Nat := η.rid) (F : List WeakMem.Ts := η.fp) (Ri : WeakMem.AllocLabel → Nat := η.rini) : TEnv :=
  { η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri, rels := fun k =>
      ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).relC (η.wit k),
           urels := fun k => ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee.relC (η.wit k),
           rrs := fun k => ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).relCR (η.wit k),
           urrs := fun k => ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee.relCR (η.wit k) }

theorem Coh_withSto {η : TEnv} (hc : Coh η) (s : WeakMem.AllocLabel → Option Cell)
    (i : WeakMem.AllocLabel → Nat := η.ini) (P : WeakMem.AllocLabel → Option WeakMem.Ts := η.pfr)
    (S : WeakMem.AllocLabel → Prop := η.seen) (Bx : WeakMem.AllocLabel → Option Box := η.box)
    (Rd : Nat := η.rid) (F : List WeakMem.Ts := η.fp) (Ri : WeakMem.AllocLabel → Nat := η.rini) : Coh (η.withSto s i P S Bx Rd F Ri) := by
  have e : CE (η.withSto s i P S Bx Rd F Ri) = CE ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv) := rfl
  have e' : CE (η.withSto s i P S Bx Rd F Ri).unsee =
      CE ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee := rfl
  intro k
  have hs := (hc k).1
  refine ⟨hs, fun ρ' S' ws => ?_, fun ρ' S' ws => ?_⟩
  · show ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).relC (η.wit k) S' ws ↔
      VR ρ' (CE (η.withSto s i P S Bx Rd F Ri)) (η.wit k) S' ws
    rw [e]
    exact VR_clo hs _ ρ' S' ws
  · show ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee.relC (η.wit k) S' ws ↔
      VR ρ' (CE (η.withSto s i P S Bx Rd F Ri).unsee) (η.wit k) S' ws
    rw [e']
    exact VR_clo hs _ ρ' S' ws

theorem CohR_withSto {η : TEnv} (hc : Coh η) (s : WeakMem.AllocLabel → Option Cell)
    (i : WeakMem.AllocLabel → Nat := η.ini) (P : WeakMem.AllocLabel → Option WeakMem.Ts := η.pfr)
    (S : WeakMem.AllocLabel → Prop := η.seen) (Bx : WeakMem.AllocLabel → Option Box := η.box)
    (Rd : Nat := η.rid) (F : List WeakMem.Ts := η.fp) (Ri : WeakMem.AllocLabel → Nat := η.rini) : CohR (η.withSto s i P S Bx Rd F Ri) := by
  have e : CE (η.withSto s i P S Bx Rd F Ri) =
      CE ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv) := rfl
  have e' : CE (η.withSto s i P S Bx Rd F Ri).unsee =
      CE ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee := rfl
  intro k
  have hs := (hc k).1
  refine ⟨fun ρ' S' ws X => ?_, fun ρ' S' ws X => ?_⟩
  · show ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).relCR (η.wit k) S' ws X ↔
      VRR ρ' (CE (η.withSto s i P S Bx Rd F Ri)) (η.wit k) S' ws X
    rw [e]; exact VRR_clo hs _ ρ' S' ws X
  · show ({ η with sto := s, ini := i, pfr := P, seen := S, box := Bx, rid := Rd, fp := F, rini := Ri } : TEnv).unsee.relCR (η.wit k)
      S' ws X ↔ VRR ρ' (CE (η.withSto s i P S Bx Rd F Ri).unsee) (η.wit k) S' ws X
    rw [e']; exact VRR_clo hs _ ρ' S' ws X

theorem Ext_withSto {η : TEnv} (hc : Coh η) {s : WeakMem.AllocLabel → Option Cell}
    (hs : ∀ l c, η.sto l = some c → s l = some c) {i : WeakMem.AllocLabel → Nat}
    (hi : ∀ l, η.ini l ≤ i l) {P : WeakMem.AllocLabel → Option WeakMem.Ts}
    {S : WeakMem.AllocLabel → Prop}
    (hP : ∀ l f, η.pfr l = some f → P l = some f := by intro _ _ h; exact h)
    (hS : ∀ l, η.seen l → S l := by intro _ h; exact h) {Bx : WeakMem.AllocLabel → Option Box}
    (hB : ∀ l B, η.box l = some B → Bx l = some B := by intro _ _ h; exact h) {Rd : Nat}
    (hR : η.rid ≤ Rd := by exact Nat.le_refl _) (F : List WeakMem.Ts := η.fp) (Ri : WeakMem.AllocLabel → Nat := η.rini)
    (hRi : ∀ l, η.rini l ≤ Ri l := by rini_le) : Ext η (η.withSto s i P S Bx Rd F Ri) :=
  ⟨Coh_withSto hc s i P S Bx Rd F Ri, rfl, rfl, rfl, hs, hi, hP, hS, hB, hR, CohR_withSto hc s i P S Bx Rd F Ri, hRi⟩

/-- Back from a callee's extension to the caller's view at the same Σ. -/
theorem Ext_back {η η₁ η' : TEnv} (hc : Coh η) (hx : Ext η₁ η') (hs : η₁.sto = η.sto)
    (hp : η₁.prog = η.prog) (ht : η₁.tid = η.tid) (hn : η₁.ini = η.ini) (hf : η₁.pfr = η.pfr)
    (hse : η₁.seen = η.seen) (hbx : η₁.box = η.box) (hrn : η₁.rini = η.rini) :
    Ext η (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini) ∧
      CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini) = CE η' := by
  refine ⟨Ext_withSto hc (fun l c h => hx.2.2.2.2.1 l c (hs ▸ h)) (fun l => hn ▸ hx.2.2.2.2.2.1 l)
    (fun l f h => hx.2.2.2.2.2.2.1 l f (hf ▸ h)) (fun l h => hx.2.2.2.2.2.2.2.1 l (hse ▸ h))
    (fun l B h => hx.2.2.2.2.2.2.2.2.1 l B (hbx ▸ h)) (Nat.le_max_left _ _) η'.fp η'.rini (fun l => hrn ▸ hx.rini l), ?_⟩
  have e1 : η'.prog = η.prog := hx.2.2.1.trans hp
  have e2 : η'.tid = η.tid := hx.2.2.2.1.trans ht
  simp only [CE, TEnv.withSto, e1, e2]

theorem VR_ext {η η' : TEnv} (hc : Coh η) (he : Ext η η') {ρ : Nat → Nat} {t : Ty} {S : Shp}
    {ws : List Word} (hv : VR ρ η t S ws) : VR ρ η' t S ws := by
  have a := VR_close hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have b := VR_close he.1 ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have hv1 : VR ρ (CE η) (cl ρ η.wit 0 0 t) S ws := a.1 hv
  have hv2 : VR ρ (CE η') (cl ρ η.wit 0 0 t) S ws :=
    VR_mono _ (CE η) (CE η') ρ S ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl he.2.2.1.symm he.2.2.2.1.symm
      he.2.2.2.2.1 he.2.2.2.2.2.1 he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.1 hv1 he.rini
  rw [← he.2.1] at hv2
  exact b.2 hv2

theorem VR_coh {η₁ η₂ : TEnv} (h1 : Coh η₁) (h2 : Coh η₂) (hw : η₁.wit = η₂.wit) (hE : CE η₁ = CE η₂)
    (ρ : Nat → Nat) (t : Ty) (S : Shp) (ws : List Word) : VR ρ η₁ t S ws ↔ VR ρ η₂ t S ws := by
  have a := VR_close h1 ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have b := VR_close h2 ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c : VR ρ (CE η₁) (cl ρ η₁.wit 0 0 t) S ws ↔ VR ρ (CE η₂) (cl ρ η₂.wit 0 0 t) S ws := by
    rw [hw, hE]
  exact a.trans (c.trans b.symm)

theorem VRR_ext {η η' : TEnv} (hc : Coh η) (hr : CohR η) (he : Ext η η') {ρ : Nat → Nat}
    {t : Ty} {S : Shp} {ws : List Word} {X : Res} (hv : VRR ρ η t S ws X) : VRR ρ η' t S ws X := by
  have a := VRR_close hc hr ρ t [] 0 ρ ρ S ws X (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have b := VRR_close he.1 he.2.2.2.2.2.2.2.2.2.2.1 ρ t [] 0 ρ ρ S ws X (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have hv1 : VRR ρ (CE η) (cl ρ η.wit 0 0 t) S ws X := a.1 hv
  have hv2 : VRR ρ (CE η') (cl ρ η.wit 0 0 t) S ws X :=
    VRR_mono _ (CE η) (CE η') ρ S ws X (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl he.2.2.1.symm
      he.2.2.2.1.symm he.2.2.2.2.1 he.2.2.2.2.2.1 he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.1 hv1 he.rini
  rw [← he.2.1] at hv2
  exact b.2 hv2

theorem VRR_coh {η₁ η₂ : TEnv} (h1 : Coh η₁) (r1 : CohR η₁) (h2 : Coh η₂) (r2 : CohR η₂) (hw : η₁.wit = η₂.wit)
    (hE : CE η₁ = CE η₂) (ρ : Nat → Nat) (t : Ty) (S : Shp) (ws : List Word) (X : Res) :
    VRR ρ η₁ t S ws X ↔ VRR ρ η₂ t S ws X := by
  have a := VRR_close h1 r1 ρ t [] 0 ρ ρ S ws X (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have b := VRR_close h2 r2 ρ t [] 0 ρ ρ S ws X (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c : VRR ρ (CE η₁) (cl ρ η₁.wit 0 0 t) S ws X ↔ VRR ρ (CE η₂) (cl ρ η₂.wit 0 0 t) S ws X := by
    rw [hw, hE]
  exact a.trans (c.trans b.symm)

/-! ### (P3) Type equality, subsumption and guarded relations for `VRR` -/

theorem IEq_ev {cx : Cx} {d : Nat} {r s : Idx} {ρ : Nat → Nat} (h : IEq cx d r s)
    (hs : d = 0 → Sat cx.facts ρ) : ev ρ r = ev ρ s := by
  rcases h with rfl | ⟨hd, he⟩
  · rfl
  · exact he ρ (hs hd)

theorem VRR_tyEq {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) :
    ∀ {η : TEnv} (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (R : Res), (d = 0 → Sat cx.facts ρ) →
      (VRR ρ η t rt ws R ↔ VRR ρ η u rt ws R) := by
  induction h with
  | refl => intros; exact Iff.rfl
  | intS h =>
      intro η ρ rt ws R hs
      simp only [VRR, IEq_ev h hs]
  | prod _ _ ih1 ih2 =>
      intro η ρ rt ws R hs
      have e1 := fun rt ws R => ih1 (η := η) ρ rt ws R hs
      have e2 := fun rt ws R => ih2 (η := η) ρ rt ws R hs
      simp only [VRR, e1, e2]
  | iex _ ih =>
      intro η ρ rt ws R _
      simp only [VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun w =>
        and_congr_right fun _ => ih (vcons w ρ) rb ws R (fun h => absurd h (Nat.succ_ne_zero _))
  | refine h' ih => intro η ρ rt ws R hs; simp only [VRR]; exact and_congr (ih ρ rt ws R hs) (by rw [TEnv.selIni_tyEq η h'])
  | refineIni h h' ih =>
      intro η ρ rt ws R hs
      simp only [VRR]
      refine and_congr (ih ρ rt ws R hs) ?_
      rw [TEnv.selIni_tyEq η h']
      simp only [IniR, IEq_ev h hs]
  | sum _ _ ih1 ih2 =>
      intro η ρ rt ws R hs
      have e1 := fun rt ws R => ih1 (η := η) ρ rt ws R hs
      have e2 := fun rt ws R => ih2 (η := η) ρ rt ws R hs
      have e3 := fun rt ws R => ih1 (η := η.unsee) ρ rt ws R hs
      have e4 := fun rt ws R => ih2 (η := η.unsee) ρ rt ws R hs
      simp only [VRR, e1, e2, e3, e4]
  | code h1 h2 _ _ =>
      intro η ρ rt ws R hs
      simp only [VRR, cl_tyEq0 h1 η.wit 0 hs, cl_tyEq0 h2 η.wit 0 hs]
  | array => intros; simp [VRR]
  | ptr hm h _ =>
      intro η ρ rt ws R hs
      simp only [VRR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm, ownW_meq hm]
  | ptrOpt hm h _ =>
      intro η ρ rt ws R hs
      simp only [VRR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm, ownW_meq hm]
  | loc hm h _ =>
      intro η ρ rt ws R hs
      simp only [VRR, cl_tyEq0 h η.wit 0 hs, ModeOK_meq (i := η.tid) hm, modeIni_meq hm, ownW_meq hm]
  | word h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs]
  | word2 h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs]
  | tok2 h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs]
  | epair => intros; simp [VRR]
  | tokE h1 h2 => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h1 hs, IEq_ev h2 hs]
  | tokNone h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs, tokWd_none, tokWd_some]
  | tokSome h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs, tokWd_none, tokWd_some]
  | share h => intro η ρ rt ws R hs; simp only [VRR, IEq_ev h hs]
  | cap => intros; simp [VRR]
  | mu h ih =>
      intro η ρ rt ws R hs
      simp only [VRR, cl_tyEq0 (TyEqS.mu h) η.wit 0 hs]
      exact ih ρ rt ws R hs
  | tex _ ih =>
      intro η ρ rt ws R hs; simp only [VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => ih ρ rb ws R hs
  | iall _ ih =>
      intro η ρ rt ws R _
      simp only [VRR]
      exact forall_congr' fun n => ih (vcons n ρ) rt ws R (fun h => absurd h (Nat.succ_ne_zero _))

theorem VRR_sub {cx : Cx} {η : TEnv} {ρ : Nat → Nat} (hs : Sat cx.facts ρ) {σ τ : Ty}
    (h : SubS cx σ τ) : ∀ rt ws R, VRR ρ η σ rt ws R → VRR ρ η τ rt ws R := by
  induction h generalizing η with
  | eq h => intro rt ws R hv; exact (VRR_tyEq h ρ rt ws R (fun _ => hs)).1 hv
  | intS => intro rt ws R hv; simp only [VRR] at hv ⊢; exact ⟨⟨_, hv.1⟩, hv.2⟩
  | refine _ ih => intro rt ws R hv; simp only [VRR] at hv; exact ih rt ws R hv.1
  | iniWeak h hl =>
      intro rt ws R hv; simp only [VRR, IniR] at hv ⊢
      exact ⟨(VRR_tyEq h ρ rt ws R (fun _ => hs)).1 hv.1, fun a ha =>
        Nat.le_trans (hl ρ hs) (by rw [← TEnv.selIni_tyEq η h]; exact hv.2 a ha)⟩
  | prod _ _ iha ihb =>
      intro rt ws R hv
      simp only [VRR] at hv ⊢
      obtain ⟨ra, rb, hr, Ra, Rb, hR, hz, hf⟩ := hv
      refine ⟨ra, rb, hr, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hf n hn
      exact ⟨h1, iha _ _ _ h2, ihb _ _ _ h3⟩
  | nonNull hm h =>
      intro rt ws R hv
      simp only [VRR] at hv ⊢
      obtain ⟨⟨a, c, h1, h2, h3, h4, h5, h6⟩, hR⟩ := hv
      refine ⟨Or.inr ⟨a, c, h1, h2, h3, (cl_tyEq0 h η.wit 0 (fun _ => hs)) ▸ h4, ?_, h6⟩, hR.trans (ownW_meq hm _)⟩
      rw [← ModeOK_meq (i := η.tid) hm]; exact h5
  | sum _ _ iha ihb =>
      intro rt ws R hv
      simp only [VRR] at hv ⊢
      obtain ⟨n, Ra, Rb, hr, ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · refine ⟨n, Ra, Rb, hr, Or.inl ⟨hb, x, s, B, hx, ho, hB, hn, hsB, hm,
          fun hj => ⟨fun e => iha _ _ _ ((hA hj).1 e), fun e => ?_⟩,
          fun hj => ⟨fun e => ihb _ _ _ ((hA' hj).1 e), fun e => ?_⟩⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, iha (η := η.unsee) _ _ _ hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA' hj).2 e
          exact ⟨q, hq, hs1, hw1, hv1, ihb (η := η.unsee) _ _ _ hv⟩
      · refine ⟨n, Ra, Rb, hr, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj; exact ⟨q, hq, iha _ _ _ hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, ihb _ _ _ hv⟩
  | cap => intro rt ws R hv; simpa [VRR] using hv

theorem VRR_relsG : ∀ (t : Ty) (c : Nat) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (R : Res),
    t.unguarded c = false → (∀ k, k ≠ c → η₁.rrs k = η₂.rrs k) → (∀ k, k ≠ c → η₁.urrs k = η₂.urrs k) →
      η₁.wit = η₂.wit → CE η₁ = CE η₂ →
      (VRR ρ η₁ t rt ws R ↔ VRR ρ η₂ t rt ws R)
  | .tvar k, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, _, _ => by
      have hk : k ≠ c := by simpa [Ty.unguarded] using hg
      simp only [VRR, hr k hk]
  | .refine t ψ, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      have e3 : η₁.ini = η₂.ini := by have h := congrArg TEnv.ini hp; exact h
      simp only [VRR, e3]; exact and_congr (VRR_relsG t c η₁ η₂ ρ rt ws R hg hr hur hw hp)
        (by rw [TEnv.selIni_eq hw e3 (by have h := congrArg TEnv.rini hp; exact h) t])
  | .iex b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun w => and_congr_right fun _ =>
        VRR_relsG b c η₁ η₂ (vcons w ρ) rb ws R hg hr hur hw hp
  | .prod a b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      have ha : ∀ rt ws R, VRR ρ η₁ a rt ws R ↔ VRR ρ η₂ a rt ws R :=
        fun rt ws R => VRR_relsG a c η₁ η₂ ρ rt ws R hg.1 hr hur hw hp
      have hb : ∀ rt ws R, VRR ρ η₁ b rt ws R ↔ VRR ρ η₂ b rt ws R :=
        fun rt ws R => VRR_relsG b c η₁ η₂ ρ rt ws R hg.2 hr hur hw hp
      simp only [VRR, ha, hb]
  | .sum a b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded, Bool.or_eq_false_iff] at hg
      have ha : ∀ rt ws R, VRR ρ η₁ a rt ws R ↔ VRR ρ η₂ a rt ws R :=
        fun rt ws R => VRR_relsG a c η₁ η₂ ρ rt ws R hg.1 hr hur hw hp
      have hb : ∀ rt ws R, VRR ρ η₁ b rt ws R ↔ VRR ρ η₂ b rt ws R :=
        fun rt ws R => VRR_relsG b c η₁ η₂ ρ rt ws R hg.2 hr hur hw hp
      have hpu : CE η₁.unsee = CE η₂.unsee := by rw [← CE_unsee, ← CE_unsee, hp]
      have ha' : ∀ rt ws R, VRR ρ η₁.unsee a rt ws R ↔ VRR ρ η₂.unsee a rt ws R :=
        fun rt ws R => VRR_relsG a c η₁.unsee η₂.unsee ρ rt ws R hg.1 hur hur hw hpu
      have hb' : ∀ rt ws R, VRR ρ η₁.unsee b rt ws R ↔ VRR ρ η₂.unsee b rt ws R :=
        fun rt ws R => VRR_relsG b c η₁.unsee η₂.unsee ρ rt ws R hg.2 hur hur hw hpu
      have e1 : η₁.box = η₂.box := by have h := congrArg TEnv.box hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e3 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      simp only [VRR, ha, hb, ha', hb', e1, e2, e3, e4]
  | .code a b, _, η₁, η₂, ρ, rt, ws, R, _, _, _, hw, hp => by
      have e : η₁.prog = η₂.prog := by have h := congrArg TEnv.prog hp; exact h
      simp only [VRR, hw, e]
  | .tex κ b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ =>
          VRR_relsG b (c + 1) (η₁.push0 s) (η₂.push0 s) ρ rb ws R hg ?_ ?_ ?_ hp
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hr k this]
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hur k this]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .int, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .tid, _, η₁, η₂, _, _, _, _, _, _, _, _, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e3 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      simp only [VRR, VR, e1, e2, e3, e4]
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .void, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .ptr _ _, _, η₁, η₂, ρ, rt, ws, R, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      simp only [VRR, hw, e1, e2, e4, e5]
  | .ptrOpt _ _, _, η₁, η₂, ρ, rt, ws, R, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      simp only [VRR, hw, e1, e2, e4, e5]
  | .loc _ _, _, η₁, η₂, ρ, rt, ws, R, _, _, _, hw, hp => by
      have e1 : η₁.sto = η₂.sto := by have h := congrArg TEnv.sto hp; exact h
      have e2 : η₁.tid = η₂.tid := by have h := congrArg TEnv.tid hp; exact h
      have e4 : η₁.pfr = η₂.pfr := by have h := congrArg TEnv.pfr hp; exact h
      have e5 : η₁.seen = η₂.seen := by have h := congrArg TEnv.seen hp; exact h
      have e3 : η₁.ini = η₂.ini := by have h := congrArg TEnv.ini hp; exact h
      have e3' : η₁.rini = η₂.rini := by have h := congrArg TEnv.rini hp; exact h
      simp only [VRR, hw, e1, e2, e3, e3', e4, e5]
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .word _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .word2 _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [VRR]
  | .mu b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VRR, hw]
      refine VRR_relsG b (c + 1) _ _ ρ rt ws R hg ?_ ?_ ?_ hp
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hr k this]
      · intro k hk
        rcases k with _ | k
        · simp [TEnv.push0, TEnv.ins, TEnv.insR]
        · have : k ≠ c := by omega
          simp [TEnv.push0, TEnv.ins, TEnv.insR, hur k this]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
  | .iall b, c, η₁, η₂, ρ, rt, ws, R, hg, hr, hur, hw, hp => by
      simp only [Ty.unguarded] at hg
      simp only [VRR]
      exact forall_congr' fun n => VRR_relsG b c η₁ η₂ (vcons n ρ) rt ws R hg hr hur hw hp

theorem map_singleton {α β : Type} {f : α → β} {l : List α} {b : β} (h : l.map f = [b]) :
    ∃ a, l = [a] ∧ f a = b := by
  match l, h with
  | [a], h => exact ⟨a, rfl, by simpa using h⟩

/-! ### Integer bodies: `VR` that ignores the runtime type -/

/-- An existential body that is an integer (possibly refined): `∃n.Int(n)`,
`∃n.{Int(n) | …}`.  Its `VR` does not look at the runtime type, so `pack` is
sound for it without shape agreement. -/
def IntBody : Ty → Prop
  | .intS _ => True
  | .int => True
  | .refine t _ => IntBody t
  | _ => False

theorem IntBody_rt {ρ : Nat → Nat} {η : TEnv} (t : Ty) (hb : IntBody t) (rt rt' : Shp)
    (ws : List Word) (h : VR ρ η t rt ws) : VR ρ η t rt' ws := by
  induction t <;> simp_all [IntBody, VR]

theorem IntBody_one {ρ : Nat → Nat} {η : TEnv} (t : Ty) (hb : IntBody t) (rt : Shp)
    (ws : List Word) (h : VR ρ η t rt ws) : ∃ w, ws = [w] := by
  induction t <;> simp only [IntBody] at hb
  case intS i =>
    simp only [VR] at h; obtain ⟨w, rfl, -⟩ := map_singleton h; exact ⟨w, rfl⟩
  case int =>
    simp only [VR] at h; obtain ⟨n, hn⟩ := h; obtain ⟨w, rfl, -⟩ := map_singleton hn; exact ⟨w, rfl⟩
  case refine t ψ ih => simp only [VR] at h; exact ih hb h.1

theorem IntBody_width (ρc : Ctx) (t : Ty) (hb : IntBody t) : (info ρc t).width = some (.lit 1) := by
  induction t <;> simp only [IntBody] at hb
  case intS => simp [info, Info.leaf]
  case int => simp [info, Info.leaf]
  case refine t ψ ih => simp only [info]; exact ih hb

theorem IntBody_accs (t : Ty) (hb : IntBody t) : accs t = some [.one] := by
  induction t <;> simp only [IntBody] at hb
  case intS => rfl
  case int => rfl
  case refine t ψ ih => simp only [accs]; exact ih hb

theorem IntBody_subst (σs : List Ty) (c d : Nat) (t : Ty) (hb : IntBody t) :
    IntBody (substTs σs c d t) := by
  induction t <;> simp only [IntBody] at hb
  case intS => simp [substTs, IntBody]
  case int => simp [substTs, IntBody]
  case refine t ψ ih => simp only [substTs, IntBody]; exact ih hb

/-! ## §2b Layouts: `accs` has exactly `width` words -/


theorem nWords_append (a b : List Acc) : nWords (a ++ b) = nWords a + nWords b := by
  simp [nWords]

theorem closed_lower (c : Nat) : ∀ w : Idx, (w.lower c).closed = w.closed
  | .lit _ => rfl
  | .var k => by simp only [Idx.lower]; split <;> rfl
  | .add i j => by simp only [Idx.lower, Idx.closed, closed_lower c i, closed_lower c j]
  | .sub i j => by simp only [Idx.lower, Idx.closed, closed_lower c i, closed_lower c j]
  | .smul n i => by simp only [Idx.lower, Idx.closed, closed_lower c i]

theorem top_cons : Ctx.cons none Ty.top = Ty.top := by funext n; cases n <;> rfl
theorem top_shiftI : Ctx.shiftI Ty.top = Ty.top := by funext n; simp [Ctx.shiftI, Ty.top]

theorem lowerW_some {o : Option Idx} {w : Idx} (h : lowerW o = some w) :
    ∃ w0, o = some w0 ∧ w.closed = w0.closed := by
  cases o with
  | none => simp [lowerW] at h
  | some w0 =>
      simp only [lowerW, Option.bind_some] at h
      split at h
      · simp at h
      · simp only [Option.some.injEq] at h; subst h; exact ⟨w0, rfl, closed_lower 0 w0⟩

/-- A coupled `∃` package is either laid out as its body, or as one access of
exactly its raw width. -/
theorem accs_iex (t : Ty) : accs (.iex t) = accs t ∨
    ∃ k, (Ty.iex t).rawWords = some k ∧ (accs (.iex t)).map nWords = some k := by
  by_cases hc : t.countI 0 ≥ 2
  · cases hr : (Ty.iex t).rawWords with
    | none => left; simp [accs, hc, hr]
    | some k =>
        match k, hr with
        | 0, hr => right; exact ⟨0, rfl, by simp [accs, hc, hr, nWords]⟩
        | 1, hr => right; exact ⟨1, rfl, by simp [accs, hc, hr, nWords, Acc.size]⟩
        | 2, hr => right; exact ⟨2, rfl, by simp [accs, hc, hr, nWords, Acc.size]⟩
        | k + 3, hr => left; simp [accs, hc, hr]
  · left; simp [accs, hc]

theorem accs_tex (κ : Kind) (t : Ty) : accs (.tex κ t) = accs t ∨
    ∃ k, (Ty.tex κ t).rawWords = some k ∧ (accs (.tex κ t)).map nWords = some k := by
  by_cases hc : t.countT 0 ≥ 2
  · cases hr : (Ty.tex κ t).rawWords with
    | none => left; simp [accs, hc, hr]
    | some k =>
        match k, hr with
        | 0, hr => right; exact ⟨0, rfl, by simp [accs, hc, hr, nWords]⟩
        | 1, hr => right; exact ⟨1, rfl, by simp [accs, hc, hr, nWords, Acc.size]⟩
        | 2, hr => right; exact ⟨2, rfl, by simp [accs, hc, hr, nWords, Acc.size]⟩
        | k + 3, hr => left; simp [accs, hc, hr]
  · left; simp [accs, hc]

theorem rawWords_iex {t : Ty} {k : Nat} (h : (Ty.iex t).rawWords = some k) :
    ∃ w0, (info Ty.top t).width = some w0 ∧ w0.closed = some k := by
  simp only [Ty.rawWords, Ty.width, info, top_shiftI] at h
  cases hl : lowerW (info Ty.top t).width with
  | none => simp [hl] at h
  | some w =>
      simp only [hl, Option.bind_some] at h
      obtain ⟨w0, hw0, hc⟩ := lowerW_some hl
      exact ⟨w0, hw0, by rw [← hc]; exact h⟩

theorem rawWords_tex {κ : Kind} {t : Ty} {k : Nat} (h : (Ty.tex κ t).rawWords = some k) :
    ∃ w0, (info Ty.top t).width = some w0 ∧ w0.closed = some k := by
  simp only [Ty.rawWords, Ty.width, info, top_cons] at h
  cases hw : (info Ty.top t).width with
  | none => simp [hw] at h
  | some w0 => simp only [hw, Option.bind_some] at h; exact ⟨w0, rfl, h⟩

/-- **Layout width.**  Whenever a type has a load/store layout and a closed
width, the layout covers exactly that many words. -/
theorem accs_width : ∀ (t : Ty) (us : List Acc), accs t = some us →
    ∀ w k, (info Ty.top t).width = some w → w.closed = some k → nWords us = k := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro us h w k hw hk
      cases ha : accs a <;> cases hb : accs b <;> simp [accs, ha, hb] at h
      rename_i ua ub
      cases hwa : (info Ty.top a).width <;> cases hwb : (info Ty.top b).width <;>
        simp [info, Info.leaf, hwa, hwb] at hw
      rename_i wa wb
      subst h; subst hw
      cases hka : wa.closed <;> cases hkb : wb.closed <;> simp [Idx.closed, hka, hkb] at hk
      rename_i ka kb
      rw [nWords_append, iha ua ha wa ka hwa hka, ihb ub hb wb kb hwb hkb]
      omega
  | sum a b _ _ =>
      intro us h w k hw hk
      simp only [accs, Ty.tier, info] at h hw
      by_cases hm : ((info Ty.top a).arms.combine (info Ty.top b).arms).maxW = none
      · simp [hm] at hw
      · cases hT : ((info Ty.top a).arms.combine (info Ty.top b).arms).tier <;>
          simp [hm, hT] at h hw <;> subst h <;> subst hw <;>
          simp [Idx.closed] at hk <;> subst hk <;> rfl
  | refine t ψ ih =>
      intro us h w k hw hk
      simp only [accs] at h; simp only [info] at hw
      exact ih us h w k hw hk
  | mu t ih =>
      intro us h w k hw hk
      simp only [accs] at h; simp only [info, top_cons] at hw
      exact ih us h w k hw hk
  | iall t ih =>
      intro us h w k hw hk
      simp only [accs] at h; simp only [info, top_shiftI] at hw
      obtain ⟨w0, hw0, hc⟩ := lowerW_some hw
      exact ih us h w0 k hw0 (by rw [← hc]; exact hk)
  | iex t ih =>
      intro us h w k hw hk
      have hr : (Ty.iex t).rawWords = some k := by simp [Ty.rawWords, Ty.width, hw, hk]
      rcases accs_iex t with e | ⟨k', hr', hm⟩
      · rw [e] at h
        obtain ⟨w0, hw0, hc⟩ := rawWords_iex hr
        exact ih us h w0 k hw0 hc
      · rw [hr] at hr'; simp only [Option.some.injEq] at hr'; subst hr'
        rw [h] at hm; simpa using hm
  | tex κ t ih =>
      intro us h w k hw hk
      have hr : (Ty.tex κ t).rawWords = some k := by simp [Ty.rawWords, Ty.width, hw, hk]
      rcases accs_tex κ t with e | ⟨k', hr', hm⟩
      · rw [e] at h
        obtain ⟨w0, hw0, hc⟩ := rawWords_tex hr
        exact ih us h w0 k hw0 hc
      · rw [hr] at hr'; simp only [Option.some.injEq] at hr'; subst hr'
        rw [h] at hm; simpa using hm
  | word r P =>
      intro us h w k hw hk
      by_cases hg : P.ghost = true <;> simp [accs, info, Info.leaf, hg] at h hw <;>
        subst h <;> subst hw <;> simp [Idx.closed] at hk <;> subst hk <;> rfl
  | word2 r P =>
      intro us h w k hw hk
      simp [accs, info, Info.leaf] at h hw
      subst h; subst hw; simp [Idx.closed] at hk; subst hk; rfl
  | epair r P =>
      intro us h w k hw hk
      simp [accs, info, Info.leaf] at h hw
      subst h; subst hw; simp [Idx.closed] at hk; subst hk; rfl
  | array i t _ => intro us h; simp [accs] at h
  | tvar _ => intro us h; simp [accs] at h
  | unit | void | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ | share _ | cap _ _ | int | tid | intS _ | code _ _ | ptr _ _ | ptrOpt _ _
    | loc _ _ | fix _ _ | lanes _ _ =>
      intro us h w k hw hk
      simp [accs, info, Info.leaf] at h hw
      subst h; subst hw
      simp [Idx.closed] at hk
      subst hk; rfl

/-- `ShapeC` survives `unpack`: the body has the package's words. -/
theorem ShapeC_iex {b : Ty} {ws : List Word} (h : ShapeC (.iex b) ws) : ShapeC b ws := by
  intro us hu
  rcases accs_iex b with e | ⟨k, hr, hm⟩
  · exact h us (by rw [e]; exact hu)
  · cases ha : accs (.iex b) with
    | none => simp [ha] at hm
    | some us' =>
        simp only [ha, Option.map_some, Option.some.injEq] at hm
        obtain ⟨w0, hw0, hc⟩ := rawWords_iex hr
        rw [h us' ha, hm, accs_width b us hu w0 k hw0 hc]

theorem IntBody_accs_iex {b : Ty} (hb : IntBody b) : ∀ us, accs (.iex b) = some us → nWords us = 1 := by
  intro us h
  rcases accs_iex b with e | ⟨k, hr, hm⟩
  · rw [e, IntBody_accs b hb] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · obtain ⟨w0, hw0, hc⟩ := rawWords_iex hr
    rw [IntBody_width _ b hb] at hw0
    simp only [Option.some.injEq] at hw0; subst hw0
    simp [Idx.closed] at hc; subst hc
    rw [h] at hm; simpa using hm

theorem shape_int (w : Word) : ShapeC .int [w] := by
  intro us h; simp [accs] at h; subst h; rfl

/-! ## §2c Index shifts do not move layouts

`push` shifts every static type in the context (`shiftI 0`); runtime types
are never shifted.  So the rendition invariant needs layouts, and hence
shapes, to be blind to index shifts: `info_shiftI` (widths move, arms do not),
then `accs_shiftI` and `shp_shiftI`.  Instantiation is different: it can turn
an array's variable extent into a literal, and so change a width (F4). -/

theorem mentions_shift (c k : Nat) (hk : k < c) : ∀ i : Idx, (i.shift c).mentions k = i.mentions k
  | .lit _ => rfl
  | .var k' => by
      by_cases h : k' ≥ c
      · simp only [Idx.shift, h, ite_true, Idx.mentions]
        have h1 : (k' + 1 == k) = false := by simp; omega
        have h2 : (k' == k) = false := by simp; omega
        rw [h1, h2]
      · simp only [Idx.shift, h, ite_false]
  | .add i j => by simp only [Idx.shift, Idx.mentions, mentions_shift c k hk i, mentions_shift c k hk j]
  | .sub i j => by simp only [Idx.shift, Idx.mentions, mentions_shift c k hk i, mentions_shift c k hk j]
  | .smul _ i => by simp only [Idx.shift, Idx.mentions, mentions_shift c k hk i]

theorem mode_mentions_shift (c k : Nat) (hk : k < c) (μ : Mode) : (μ.shift c).mentions k = μ.mentions k := by
  cases μ <;> simp [Mode.shift, Mode.mentions, mentions_shift c k hk]

theorem pred_mentions_shift (c k : Nat) (hk : k < c) : ∀ ψ : Pred, (ψ.shift c).mentions k = ψ.mentions k
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.mentions, mentions_shift c k hk]
  | .eq i j => by simp only [Pred.shift, Pred.mentions, mentions_shift c k hk]
  | .and p q => by simp only [Pred.shift, Pred.mentions, pred_mentions_shift c k hk p, pred_mentions_shift c k hk q]
  | .ini i => by simp only [Pred.shift, Pred.mentions, mentions_shift c k hk]

theorem idxMentions_shiftI : ∀ (t : Ty) (c k : Nat), k < c → (t.shiftI c).idxMentions k = t.idxMentions k := by
  intro t
  induction t with
  | intS i => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | prod a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | sum a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | code a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | array i t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, mentions_shift c k hk]
  | ptr μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, mode_mentions_shift c k hk]
  | ptrOpt μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, mode_mentions_shift c k hk]
  | loc μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, mode_mentions_shift c k hk]
  | word r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | tok r i =>
      intro c k hk
      rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | word2 r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | tok2 r P i j => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | epair r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | tokE r P i => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | share r => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | cap s r => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mentions_shift c k hk]
  | mu t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk]
  | tex κ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk]
  | iall t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | iex t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | refine t ψ ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, pred_mentions_shift c k hk]
  | _ => intros; rfl

theorem tyMentions_shiftI : ∀ (t : Ty) (c k : Nat), (t.shiftI c).tyMentions k = t.tyMentions k := by
  intro t
  induction t <;> intro c k <;> simp_all [Ty.shiftI, Ty.tyMentions]

theorem countT_shiftI : ∀ (t : Ty) (c k : Nat), (t.shiftI c).countT k = t.countT k
  | .prod a b, c, k => by simp only [Ty.shiftI, Ty.countT, countT_shiftI a c k, countT_shiftI b c k]
  | .refine t ψ, c, k => by simp only [Ty.shiftI, Ty.countT, countT_shiftI t c k]
  | .iall t, c, k => by simp only [Ty.shiftI, Ty.countT, countT_shiftI t (c + 1) k]
  | .iex t, c, k => by simp only [Ty.shiftI, Ty.countT, countT_shiftI t (c + 1) k]
  | .tex κ t, c, k => by simp only [Ty.shiftI, Ty.countT, countT_shiftI t c (k + 1)]
  | .unit, c, k => by
      have h := tyMentions_shiftI (.unit) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .void, c, k => by
      have h := tyMentions_shiftI (.void) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .int, c, k => by
      have h := tyMentions_shiftI (.int) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .tid, c, k => by
      have h := tyMentions_shiftI (.int) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .intS i, c, k => by
      have h := tyMentions_shiftI (.intS i) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .fix sg w, c, k => by
      have h := tyMentions_shiftI (.fix sg w) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .lanes sg w, c, k => by
      have h := tyMentions_shiftI (.lanes sg w) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .sum a b, c, k => by
      have h := tyMentions_shiftI (.sum a b) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .code a b, c, k => by
      have h := tyMentions_shiftI (.code a b) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .array i t, c, k => by
      have h := tyMentions_shiftI (.array i t) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .ptr μ t, c, k => by
      have h := tyMentions_shiftI (.ptr μ t) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .ptrOpt μ t, c, k => by
      have h := tyMentions_shiftI (.ptrOpt μ t) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .loc μ t, c, k => by
      have h := tyMentions_shiftI (.loc μ t) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .word r P, c, k => by
      have h := tyMentions_shiftI (.word r P) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .tok r i, c, k => by
      have h := tyMentions_shiftI (.tok r i) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .word2 r P, c, k => by
      have h := tyMentions_shiftI (.word2 r P) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .tok2 r P i j, c, k => by
      have h := tyMentions_shiftI (.tok2 r P i j) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .epair r P, c, k => by
      have h := tyMentions_shiftI (.epair r P) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .tokE r P i, c, k => by
      have h := tyMentions_shiftI (.tokE r P i) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .share r, c, k => by
      have h := tyMentions_shiftI (.share r) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .cap s r, c, k => by
      have h := tyMentions_shiftI (.cap s r) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .tvar j, c, k => by
      have h := tyMentions_shiftI (.tvar j) c k
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countT, h])
  | .mu t, c, k => by
      simp only [Ty.shiftI, Ty.countT, countT_shiftI t c (k + 1), countT_shiftI t c 0,
        tyMentions_shiftI t c (k + 1)]

theorem countI_shiftI : ∀ (t : Ty) (c k : Nat), k < c → (t.shiftI c).countI k = t.countI k
  | .prod a b, c, k, hk => by simp only [Ty.shiftI, Ty.countI, countI_shiftI a c k hk, countI_shiftI b c k hk]
  | .refine t ψ, c, k, hk => by
      simp only [Ty.shiftI, Ty.countI, countI_shiftI t c k hk, pred_mentions_shift c k hk]
  | .iall t, c, k, hk => by simp only [Ty.shiftI, Ty.countI, countI_shiftI t (c + 1) (k + 1) (by omega)]
  | .iex t, c, k, hk => by simp only [Ty.shiftI, Ty.countI, countI_shiftI t (c + 1) (k + 1) (by omega)]
  | .unit, c, k, hk => by
      have h := idxMentions_shiftI (.unit) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .void, c, k, hk => by
      have h := idxMentions_shiftI (.void) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .int, c, k, hk => by
      have h := idxMentions_shiftI (.int) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .tid, c, k, hk => by
      have h := idxMentions_shiftI (.int) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .intS i, c, k, hk => by
      have h := idxMentions_shiftI (.intS i) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .fix sg w, c, k, hk => by
      have h := idxMentions_shiftI (.fix sg w) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .lanes sg w, c, k, hk => by
      have h := idxMentions_shiftI (.lanes sg w) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .sum a b, c, k, hk => by
      have h := idxMentions_shiftI (.sum a b) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .code a b, c, k, hk => by
      have h := idxMentions_shiftI (.code a b) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .array i t, c, k, hk => by
      have h := idxMentions_shiftI (.array i t) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .ptr μ t, c, k, hk => by
      have h := idxMentions_shiftI (.ptr μ t) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .ptrOpt μ t, c, k, hk => by
      have h := idxMentions_shiftI (.ptrOpt μ t) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .loc μ t, c, k, hk => by
      have h := idxMentions_shiftI (.loc μ t) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .word r P, c, k, hk => by
      have h := idxMentions_shiftI (.word r P) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .tok r i, c, k, hk => by
      have h := idxMentions_shiftI (.tok r i) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .word2 r P, c, k, hk => by
      have h := idxMentions_shiftI (.word2 r P) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .tok2 r P i j, c, k, hk => by
      have h := idxMentions_shiftI (.tok2 r P i j) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .epair r P, c, k, hk => by
      have h := idxMentions_shiftI (.epair r P) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .tokE r P i, c, k, hk => by
      have h := idxMentions_shiftI (.tokE r P i) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .share r, c, k, hk => by
      have h := idxMentions_shiftI (.share r) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .cap s r, c, k, hk => by
      have h := idxMentions_shiftI (.cap s r) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .tvar j, c, k, hk => by
      have h := idxMentions_shiftI (.tvar j) c k hk
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [Ty.countI, h])
  | .mu t, c, k, hk => by
      simp only [Ty.shiftI, Ty.countI, countI_shiftI t c k hk, countT_shiftI t c 0,
        idxMentions_shiftI t c k hk]
  | .tex κ t, c, k, hk => by simp only [Ty.shiftI, Ty.countI, countI_shiftI t c k hk]

theorem closed_shift (c : Nat) : ∀ w : Idx, (w.shift c).closed = w.closed
  | .lit _ => rfl
  | .var k => by simp only [Idx.shift]; split <;> rfl
  | .add i j => by simp only [Idx.shift, Idx.closed, closed_shift c i, closed_shift c j]
  | .sub i j => by simp only [Idx.shift, Idx.closed, closed_shift c i, closed_shift c j]
  | .smul n i => by simp only [Idx.shift, Idx.closed, closed_shift c i]

theorem lower_shift (c : Nat) : ∀ w : Idx, w.mentions 0 = false →
    (w.shift (c + 1)).lower 0 = (w.lower 0).shift c
  | .lit _, _ => rfl
  | .var k, h => by
      have hk : k ≠ 0 := by simpa [Idx.mentions] using h
      have e2 : k > 0 := by omega
      by_cases h1 : k ≥ c + 1
      · have e3 : k - 1 ≥ c := by omega
        simp [Idx.shift, Idx.lower, h1, e2, e3] <;> omega
      · have e3 : ¬ (k - 1 ≥ c) := by omega
        simp [Idx.shift, Idx.lower, h1, e2, e3]
  | .add i j, h => by
      simp only [Idx.mentions, Bool.or_eq_false_iff] at h
      simp only [Idx.shift, Idx.lower, lower_shift c i h.1, lower_shift c j h.2]
  | .sub i j, h => by
      simp only [Idx.mentions, Bool.or_eq_false_iff] at h
      simp only [Idx.shift, Idx.lower, lower_shift c i h.1, lower_shift c j h.2]
  | .smul n i, h => by
      simp only [Idx.mentions] at h
      simp only [Idx.shift, Idx.lower, lower_shift c i h]

theorem lowerW_shift (c : Nat) (o : Option Idx) :
    lowerW (o.map (Idx.shift (c + 1))) = (lowerW o).map (Idx.shift c) := by
  cases o with
  | none => rfl
  | some w =>
      simp only [lowerW, Option.map_some, Option.bind_some, mentions_shift (c + 1) 0 (by omega)]
      cases hm : w.mentions 0
      · simp [lower_shift c w hm]
      · simp

theorem leaf_shift (c : Nat) (o : Option Idx) : Arms.leaf (o.map (Idx.shift c)) = Arms.leaf o := by
  cases o with
  | none => rfl
  | some w => simp only [Arms.leaf, Option.map_some, Option.bind_some, closed_shift]

/-- **Index shifts move widths and nothing else.** -/
theorem info_shiftI : ∀ (t : Ty) (c : Nat),
    info Ty.top (t.shiftI c) = ⟨(info Ty.top t).width.map (Idx.shift c), (info Ty.top t).arms⟩ := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c
      simp only [Ty.shiftI, info, iha c, ihb c, Info.leaf]
      cases (info Ty.top a).width <;> cases (info Ty.top b).width <;>
        simp [Arms.leaf, closed_shift, Idx.shift, Idx.closed]
  | sum a b iha ihb =>
      intro c
      simp only [Ty.shiftI, info, iha c, ihb c]
      split <;> (try split) <;> simp_all [Idx.shift]
  | array i t _ => intro c; rfl
  | mu t ih => intro c; simp only [Ty.shiftI, info, top_cons, ih c]
  | tex κ t ih => intro c; simp only [Ty.shiftI, info, top_cons, ih c]
  | iall t ih => intro c; simp only [Ty.shiftI, info, top_shiftI, ih (c + 1), lowerW_shift]
  | iex t ih => intro c; simp only [Ty.shiftI, info, top_shiftI, ih (c + 1), lowerW_shift]
  | refine t ψ ih => intro c; simp only [Ty.shiftI, info, ih c]
  | word r P => intro c; simp only [Ty.shiftI, info, Info.leaf]; rfl
  | word2 r P => intro c; first | rfl | (simp only [Ty.shiftI, info, Info.leaf]; rfl)
  | epair r P => intro c; first | rfl | (simp only [Ty.shiftI, info, Info.leaf]; rfl)
  | tvar k => intro c; rfl
  | _ => intro c; rfl

theorem rawWords_shiftI (t : Ty) (c : Nat) : (t.shiftI c).rawWords = t.rawWords := by
  simp only [Ty.rawWords, Ty.width, info_shiftI]
  cases (info Ty.top t).width <;> simp [closed_shift]

theorem tier_shiftI (t : Ty) (c : Nat) : (t.shiftI c).tier = t.tier := by
  simp only [Ty.tier, info_shiftI]

/-- **Index shifts do not move layouts.** -/
theorem accs_shiftI : ∀ (t : Ty) (c : Nat), accs (t.shiftI c) = accs t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp only [Ty.shiftI, accs, iha c, ihb c]
  | refine t ψ ih => intro c; simp only [Ty.shiftI, accs, ih c]
  | iall t ih => intro c; simp only [Ty.shiftI, accs, ih (c + 1)]
  | mu t ih => intro c; simp only [Ty.shiftI, accs, ih c]
  | iex t ih =>
      intro c
      have hr := rawWords_shiftI (.iex t) c
      simp only [Ty.shiftI] at hr
      simp only [Ty.shiftI, accs, countI_shiftI t (c + 1) 0 (by omega), hr, ih (c + 1)]
  | tex κ t ih =>
      intro c
      have hr := rawWords_shiftI (.tex κ t) c
      simp only [Ty.shiftI] at hr
      simp only [Ty.shiftI, accs, countT_shiftI t c 0, hr, ih c]
  | sum a b _ _ =>
      intro c
      have ht := tier_shiftI (.sum a b) c
      simp only [Ty.shiftI] at ht
      simp only [Ty.shiftI, accs, ht]
  | _ => intro c; rfl

theorem wc_shiftI (t : Ty) (c : Nat) : wc (t.shiftI c) = wc t := by
  simp only [wc, accs_shiftI]

theorem skelM_shift (c : Nat) (μ : Mode) : skelM (μ.shift c) = skelM μ := by cases μ <;> rfl

theorem skelM_inst (us : List Idx) (d : Nat) (μ : Mode) : skelM (instM us d μ) = skelM μ := by
  cases μ <;> rfl

theorem skel_shiftI : ∀ (t : Ty) (c : Nat), skel (t.shiftI c) = skel t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp only [Ty.shiftI, skel, iha, ihb]
  | sum a b iha ihb => intro c; simp only [Ty.shiftI, skel, iha, ihb]
  | code a b iha ihb => intro c; simp only [Ty.shiftI, skel, iha, ihb]
  | array i t ih => intro c; simp only [Ty.shiftI, skel, ih]
  | ptr μ t ih => intro c; simp only [Ty.shiftI, skel, ih, skelM_shift]
  | ptrOpt μ t ih => intro c; simp only [Ty.shiftI, skel, ih, skelM_shift]
  | loc μ t ih => intro c; simp only [Ty.shiftI, skel, ih, skelM_shift]
  | mu t ih => intro c; simp only [Ty.shiftI, skel, ih]
  | tex κ t ih => intro c; simp only [Ty.shiftI, skel, ih]
  | iall t ih => intro c; simp only [Ty.shiftI, skel, ih]
  | iex t ih => intro c; simp only [Ty.shiftI, skel, ih]
  | refine t ψ ih => intro c; simp only [Ty.shiftI, skel, ih]
  | _ => intro c; rfl

theorem skelM_idem (μ : Mode) : skelM (skelM μ) = skelM μ := by cases μ <;> rfl

theorem skel_rf (x : Ty) : skel (rf x) = rf (skel x) := by cases x <;> rfl

theorem skel_idem : ∀ t : Ty, skel (skel t) = skel t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [skel, iha, ihb]
  | sum a b iha ihb => simp only [skel, iha, ihb]
  | code a b iha ihb => simp only [skel, iha, ihb]
  | array i t ih => simp only [skel, ih]
  | ptr μ t ih => simp only [skel, ih, skelM_idem]
  | ptrOpt μ t ih => simp only [skel, ih, skelM_idem]
  | loc μ t ih => simp only [skel, ih, skelM_idem]
  | mu t ih => simp only [skel, ih]
  | tex κ t ih => simp only [skel, ih]
  | iall t ih => simp only [skel, ih]
  | iex t ih => simp only [skel, ih]
  | refine t ψ ih => simp only [skel, skel_rf, ih]
  | _ => rfl

theorem er_rf (t : Ty) : er (rf t) = rf (er t) := by cases t <;> rfl

theorem er_idem : ∀ t : Ty, er (er t) = er t := by
  intro t; induction t <;> simp_all [er]

theorem skel_er : ∀ t : Ty, skel (er t) = er (skel t) := by
  intro t; induction t <;> simp_all [er, skel, er_rf]

theorem sig_idem (t : Ty) : sig (sig t) = sig t := by simp only [sig, skel_er, skel_idem, er_idem]

theorem sig_skel (t : Ty) : sig (skel t) = sig t := by simp only [sig, skel_idem]

theorem sig_shiftI (t : Ty) (c : Nat) : sig (t.shiftI c) = sig t := by simp only [sig, skel_shiftI]

theorem lnorm_shiftI : ∀ (t : Ty) (c : Nat), lnorm (t.shiftI c) = lnorm t := by
  intro t; induction t <;> intro c <;> simp_all [Ty.shiftI, lnorm, sig_shiftI]

/-- A runtime type's shape does not see index shifts. -/
theorem shp_shiftI : ∀ (t : Ty) (c : Nat), shp (t.shiftI c) = shp t
  | .prod a b, c => by simp only [Ty.shiftI, shp, shp_shiftI a c, shp_shiftI b c]
  | .iex b, c => by
      have h := wc_shiftI (.iex b) c
      simp only [Ty.shiftI] at h
      simp only [Ty.shiftI, shp, h, shp_shiftI b (c + 1)]
  | .refine t ψ, c => by simp only [Ty.shiftI, shp, shp_shiftI t c]
  | .fix _ _, _ => rfl
  | .lanes _ _, _ => rfl
  | .unit, c => by
      have h := wc_shiftI (.unit) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .void, c => by
      have h := wc_shiftI (.void) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .int, c => by
      have h := wc_shiftI (.int) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .tid, c => by
      have h := wc_shiftI (.int) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .intS i, c => by
      have h := wc_shiftI (.intS i) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .sum a b, c => by
      have h := wc_shiftI (.sum a b) c
      simp only [Ty.shiftI] at h ⊢
      simp only [shp, h, lnorm, lnorm_shiftI]
  | .code a b, c => by simp only [Ty.shiftI, shp, sig_shiftI]
  | .array i t, c => by
      have h := wc_shiftI (.array i t) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .ptr μ t, c => by
      have h := wc_shiftI (.ptr μ t) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .ptrOpt μ t, c => by
      have h := wc_shiftI (.ptrOpt μ t) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .loc μ t, c => by
      have h := wc_shiftI (.loc μ t) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .word r P, c => by
      have h := wc_shiftI (.word r P) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .tok r i, c => by
      have h := wc_shiftI (.tok r i) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .word2 r P, c => by
      have h := wc_shiftI (.word2 r P) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .tok2 r P i j, c => by
      have h := wc_shiftI (.tok2 r P i j) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .epair r P, c => by
      have h := wc_shiftI (.epair r P) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .tokE r P i, c => by
      have h := wc_shiftI (.tokE r P i) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .share r, c => by
      have h := wc_shiftI (.share r) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .cap s r, c => by
      have h := wc_shiftI (.cap s r) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .tvar j, c => by
      have h := wc_shiftI (.tvar j) c
      first | rfl | (simp only [Ty.shiftI] at h ⊢ <;> simp only [shp, h])
  | .mu t, c => by simp only [Ty.shiftI, shp]; exact shp_shiftI t c
  | .tex κ t, c => by
      have h := wc_shiftI (.tex κ t) c
      simp only [Ty.shiftI] at h
      simp only [Ty.shiftI, shp, h, shp_shiftI t c]
  | .iall t, c => by simp only [Ty.shiftI, shp]; exact shp_shiftI t (c + 1)

/-! ## §2d Skeletons: what layouts and shapes read

`skel` erases everything a layout cannot see: index terms (so `Int(i)` is
`Int`), regions, predicates, a token's origin, and a refinement of an integer.
Layouts (`info`, `wc`) and shapes (`shp`) factor through it, and it absorbs
index shifts, index instantiation, and the index depth of a type substitution.
So runtime types built from different static renditions of the same value —
`close σs b` after an `unpack`, `close σs (b.shiftI 0)` after a `push`, a
`pack`'s `close σs (∃b)` against its source's `close σs b[i]` — have one
skeleton, hence one shape and one word count.

The frame invariant (§3) asks each runtime type to have its static type's
skeleton.  A skeleton keeps every head the machine matches on (pairs, packages,
fixed-width words, pointers, sums), so that is also what makes the machine's
syntactic matches succeed. -/

/-- Type substitution on skeletons: no index depth to track. -/
def substS (σs : List Ty) (c : Nat) : Ty → Ty
  | .tvar k      => if k < c then .tvar k else
                      match σs[k - c]? with
                      | some σ => shiftTN c σ
                      | none   => .tvar (k - σs.length)
  | .prod a b    => .prod (substS σs c a) (substS σs c b)
  | .sum a b     => .sum (substS σs c a) (substS σs c b)
  | .code a b    => .code (substS σs c a) (substS σs c b)
  | .array i t   => .array i (substS σs c t)
  | .ptr μ t     => .ptr μ (substS σs c t)
  | .ptrOpt μ t  => .ptrOpt μ (substS σs c t)
  | .loc μ t     => .loc μ (substS σs c t)
  | .mu t        => .mu (substS σs (c + 1) t)
  | .tex κ t     => .tex κ (substS σs (c + 1) t)
  | .iall t      => .iall (substS σs c t)
  | .iex t       => .iex (substS σs c t)
  | .refine t _  => rf (substS σs c t)
  | t            => t

theorem info_rf (ρ : Ctx) (t : Ty) : info ρ (rf t) = info ρ t := by cases t <;> rfl
theorem accs_rf (t : Ty) : accs (rf t) = accs t := by cases t <;> rfl
theorem wc_rf (t : Ty) : wc (rf t) = wc t := by simp only [wc, accs_rf]
theorem shp_rf (t : Ty) : shp (rf t) = shp t := by cases t <;> rfl
theorem substS_rf (σs : List Ty) (c : Nat) (t : Ty) : substS σs c (rf t) = rf (substS σs c t) := by
  cases t <;> rfl
theorem shiftT_rf (c : Nat) (t : Ty) : (rf t).shiftT c = rf (t.shiftT c) := by
  cases t with
  | tvar k => by_cases h : k ≥ c <;> simp [rf, Ty.shiftT, h]
  | _ => rfl
theorem rf_cases (t : Ty) : rf t = .int ∨ ∃ u, rf t = .refine u .tt := by
  cases t <;> simp [rf]

theorem info_skel : ∀ (t : Ty) (ρ : Ctx), info ρ (skel t) = info ρ t := by
  intro t
  induction t with
  | prod a b iha ihb => intro ρ; simp only [skel, info, iha, ihb]
  | sum a b iha ihb => intro ρ; simp only [skel, info, iha, ihb]
  | mu t ih => intro ρ; simp only [skel, info, ih]
  | tex κ t ih => intro ρ; simp only [skel, info, ih]
  | iall t ih => intro ρ; simp only [skel, info, ih]
  | iex t ih => intro ρ; simp only [skel, info, ih]
  | refine t ψ ih => intro ρ; simp only [skel, info_rf, info, ih]
  | ptr μ t _ => intro ρ; rfl
  | ptrOpt μ t _ => intro ρ; rfl
  | loc μ t _ => intro ρ; rfl
  | array i t _ => intro ρ; rfl
  | code a b _ _ => intro ρ; rfl
  | _ => intro ρ; rfl

theorem skel_shiftIN : ∀ (d : Nat) (t : Ty), skel (shiftIN d t) = skel t
  | 0, _ => rfl
  | d + 1, t => by simp only [shiftIN, skel_shiftI, skel_shiftIN d t]

theorem skel_instT (us : List Idx) : ∀ (t : Ty) (d : Nat), skel (instT us d t) = skel t := by
  intro t
  induction t with
  | prod a b iha ihb => intro d; simp only [instT, skel, iha, ihb]
  | sum a b iha ihb => intro d; simp only [instT, skel, iha, ihb]
  | code a b iha ihb => intro d; simp only [instT, skel, iha, ihb]
  | array i t ih => intro d; simp only [instT, skel, ih]
  | ptr μ t ih => intro d; simp only [instT, skel, ih, skelM_inst]
  | ptrOpt μ t ih => intro d; simp only [instT, skel, ih, skelM_inst]
  | loc μ t ih => intro d; simp only [instT, skel, ih, skelM_inst]
  | mu t ih => intro d; simp only [instT, skel, ih]
  | tex κ t ih => intro d; simp only [instT, skel, ih]
  | iall t ih => intro d; simp only [instT, skel, ih]
  | iex t ih => intro d; simp only [instT, skel, ih]
  | refine t ψ ih => intro d; simp only [instT, skel, ih]
  | _ => intro d; rfl

theorem skel_shiftT : ∀ (t : Ty) (c : Nat), skel (t.shiftT c) = (skel t).shiftT c := by
  intro t
  induction t with
  | tvar k => intro c; by_cases h : k ≥ c <;> simp [Ty.shiftT, skel, h]
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, skel, iha, ihb]
  | sum a b iha ihb => intro c; simp only [Ty.shiftT, skel, iha, ihb]
  | code a b iha ihb => intro c; simp only [Ty.shiftT, skel, iha, ihb]
  | array i t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | ptr μ t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | ptrOpt μ t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | loc μ t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | mu t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | tex κ t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | iall t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | iex t ih => intro c; simp only [Ty.shiftT, skel, ih]
  | refine t ψ ih => intro c; simp only [Ty.shiftT, skel, ih, shiftT_rf]
  | _ => intro c; rfl

theorem skel_shiftTN : ∀ (c : Nat) (t : Ty), skel (shiftTN c t) = shiftTN c (skel t)
  | 0, _ => rfl
  | c + 1, t => by simp only [shiftTN, skel_shiftT, skel_shiftTN c t]

/-- **Skeletons of substitutions** do not depend on the index depth. -/
theorem skel_substTs (σs : List Ty) : ∀ (t : Ty) (c d : Nat),
    skel (substTs σs c d t) = substS (σs.map skel) c (skel t) := by
  intro t
  induction t with
  | tvar k =>
      intro c d
      simp only [substTs, skel, substS]
      split
      · rfl
      · rw [List.getElem?_map]
        cases σs[k - c]? with
        | none => simp [skel]
        | some σ => simp [skel_shiftIN, skel_shiftTN]
  | prod a b iha ihb => intro c d; simp only [substTs, skel, substS, iha, ihb]
  | sum a b iha ihb => intro c d; simp only [substTs, skel, substS, iha, ihb]
  | code a b iha ihb => intro c d; simp only [substTs, skel, substS, iha, ihb]
  | array i t ih => intro c d; simp only [substTs, skel, substS, ih]
  | ptr μ t ih => intro c d; simp only [substTs, skel, substS, ih]
  | ptrOpt μ t ih => intro c d; simp only [substTs, skel, substS, ih]
  | loc μ t ih => intro c d; simp only [substTs, skel, substS, ih]
  | mu t ih => intro c d; simp only [substTs, skel, substS, ih]
  | tex κ t ih => intro c d; simp only [substTs, skel, substS, ih]
  | iall t ih => intro c d; simp only [substTs, skel, substS, ih]
  | iex t ih => intro c d; simp only [substTs, skel, substS, ih]
  | refine t ψ ih => intro c d; simp only [substTs, skel, substS_rf, ih]
  | _ => intro c d; rfl

theorem skel_subst_eq {t u : Ty} (h : skel t = skel u) (σs : List Ty) (c d d' : Nat) :
    skel (substTs σs c d t) = skel (substTs σs c d' u) := by
  rw [skel_substTs, skel_substTs, h]

/-! ### 24e: substitution facts for `packT` and `unpackT` -/

theorem shiftT_unit (c : Nat) : Ty.shiftT c .unit = .unit := rfl
theorem shiftI_unit (c : Nat) : Ty.shiftI c .unit = .unit := rfl

theorem shiftTN_unit : ∀ n, shiftTN n .unit = .unit
  | 0 => rfl
  | n + 1 => by simp only [shiftTN, shiftTN_unit n]; rfl

theorem shiftIN_unit : ∀ n, shiftIN n .unit = .unit
  | 0 => rfl
  | n + 1 => by simp only [shiftIN, shiftIN_unit n]; rfl

theorem er_shiftT : ∀ (t : Ty) (c : Nat), er (t.shiftT c) = er t := by
  intro t
  induction t with
  | tvar k => intro c; by_cases h : k ≥ c <;> simp [Ty.shiftT, er, h]
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, er, iha, ihb]
  | sum a b iha ihb => intro c; simp only [Ty.shiftT, er, iha, ihb]
  | code a b iha ihb => intro c; simp only [Ty.shiftT, er, iha, ihb]
  | array i t ih => intro c; simp only [Ty.shiftT, er, ih]
  | ptr μ t _ => intro c; rfl
  | ptrOpt μ t _ => intro c; rfl
  | loc μ t _ => intro c; rfl
  | mu t ih => intro c; simp only [Ty.shiftT, er, ih]
  | tex κ t ih => intro c; simp only [Ty.shiftT, er, ih]
  | iall t ih => intro c; simp only [Ty.shiftT, er, ih]
  | iex t ih => intro c; simp only [Ty.shiftT, er, ih]
  | refine t ψ ih => intro c; simp only [Ty.shiftT, er, ih]
  | _ => intro c; rfl

theorem sig_shiftT (t : Ty) (c : Nat) : sig (t.shiftT c) = sig t := by
  simp only [sig, skel_shiftT, er_shiftT]

theorem sig_shiftTN : ∀ (n : Nat) (t : Ty), sig (shiftTN n t) = sig t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftTN, sig_shiftT, sig_shiftTN n t]

theorem sig_shiftIN : ∀ (n : Nat) (t : Ty), sig (shiftIN n t) = sig t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftIN, sig_shiftI, sig_shiftIN n t]

/-- **What a package's signature sees** (24e `packT`): substituting a guarded
variable changes only pointees and variable numbers, which `sig` erases. -/
theorem sig_pack (σs : List Ty) : ∀ (t : Ty) (c d : Nat) (s : Ty), t.guardT c = true →
    sig (substTs σs c d (Ty.substT c s t)) = sig (substTs σs (c + 1) d t) := by
  intro t
  induction t with
  | tvar k =>
      intro c d s hg
      have hk : k ≠ c := by simpa [Ty.guardT] using hg
      by_cases h1 : k < c
      · have h2 : ¬ k > c := by omega
        have h3 : k < c + 1 := by omega
        simp [Ty.substT, substTs, h1, h2, h3, hk]
      · obtain ⟨m, rfl⟩ : ∃ m, k = c + m + 1 := ⟨k - c - 1, by omega⟩
        have e : Ty.substT c s (.tvar (c + m + 1)) = .tvar (c + m) := by
          have h2 : c + m + 1 ≠ c := by omega
          have h3 : c < c + m + 1 := by omega
          simp [Ty.substT, h2, h3]
        rw [e]
        have h4 : ¬ c + m < c := by omega
        have h5 : ¬ c + m + 1 < c + 1 := by omega
        have e1 : c + m - c = m := by omega
        have e2 : c + m + 1 - (c + 1) = m := by omega
        simp only [substTs, h4, h5, e1, e2, if_false]
        cases σs[m]? with
        | none => rfl
        | some σ => simp only [sig_shiftIN, sig_shiftTN]
  | prod a b iha ihb =>
      intro c d s hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at iha ihb ⊢
      rw [iha c d s hg.1, ihb c d s hg.2]
  | sum a b iha ihb =>
      intro c d s hg
      simp only [Ty.guardT, Bool.and_eq_true] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at iha ihb ⊢
      rw [iha c d s hg.1, ihb c d s hg.2]
  | code a b iha ihb =>
      intro c d s _
      simp only [Ty.substT, substTs, sig, skel, er]
  | array i t ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at ih ⊢
      rw [ih c d s hg]
  | ptr μ t _ => intro c d s _; rfl
  | ptrOpt μ t _ => intro c d s _; rfl
  | loc μ t _ => intro c d s _; rfl
  | mu t ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at ih ⊢
      rw [ih (c + 1) d (s.shiftT 0) hg]
  | tex κ t ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at ih ⊢
      rw [ih (c + 1) d (s.shiftT 0) hg]
  | iall t ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at ih ⊢
      rw [ih c (d + 1) (s.shiftI 0) hg]
  | iex t ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er] at ih ⊢
      rw [ih c (d + 1) (s.shiftI 0) hg]
  | refine t ψ ih =>
      intro c d s hg
      simp only [Ty.guardT] at hg
      simp only [Ty.substT, substTs, sig, skel, er, er_rf] at ih ⊢
      rw [ih c d s hg]
  | _ => intro c d s _; rfl

/-- `unpackT` runs the body at `Unit` for the witness: substituting it first is
substituting it with the frame's other type arguments. -/
theorem substTs_substT_unit (σs : List Ty) : ∀ (t : Ty) (c d : Nat),
    substTs σs c d (Ty.substT c .unit t) = substTs (.unit :: σs) c d t := by
  intro t
  induction t with
  | tvar k =>
      intro c d
      rcases Nat.lt_trichotomy k c with h | rfl | h
      · have h2 : ¬ k > c := by omega
        have h3 : k ≠ c := by omega
        simp [Ty.substT, substTs, h, h2, h3]
      · simp [Ty.substT, substTs, shiftTN_unit, shiftIN_unit]
      · obtain ⟨m, rfl⟩ : ∃ m, k = c + m + 1 := ⟨k - c - 1, by omega⟩
        have e : Ty.substT c .unit (.tvar (c + m + 1)) = .tvar (c + m) := by
          have h2 : c + m + 1 ≠ c := by omega
          have h3 : c < c + m + 1 := by omega
          simp [Ty.substT, h2, h3]
        rw [e]
        have h4 : ¬ c + m < c := by omega
        have h5 : ¬ c + m + 1 < c := by omega
        have e1 : c + m - c = m := by omega
        have e2 : c + m + 1 - c = m + 1 := by omega
        simp only [substTs, h4, h5, e1, e2, if_false, List.getElem?_cons_succ, List.length_cons]
        cases σs[m]? with
        | none => simp only [Ty.tvar.injEq]; omega
        | some σ => rfl
  | prod a b iha ihb => intro c d; simp only [Ty.substT, substTs, iha, ihb]
  | sum a b iha ihb => intro c d; simp only [Ty.substT, substTs, iha, ihb]
  | code a b iha ihb => intro c d; simp only [Ty.substT, substTs, iha, ihb]
  | array i t ih => intro c d; simp only [Ty.substT, substTs, ih]
  | ptr μ t ih => intro c d; simp only [Ty.substT, substTs, ih]
  | ptrOpt μ t ih => intro c d; simp only [Ty.substT, substTs, ih]
  | loc μ t ih => intro c d; simp only [Ty.substT, substTs, ih]
  | mu t ih => intro c d; simp only [Ty.substT, substTs, shiftT_unit, ih]
  | tex κ t ih => intro c d; simp only [Ty.substT, substTs, shiftT_unit, ih]
  | iall t ih => intro c d; simp only [Ty.substT, substTs, shiftI_unit, ih]
  | iex t ih => intro c d; simp only [Ty.substT, substTs, shiftI_unit, ih]
  | refine t ψ ih => intro c d; simp only [Ty.substT, substTs, ih]
  | _ => intro c d; rfl

theorem substT_rf_unit (j : Nat) (u : Ty) : Ty.substT j .unit (rf u) = rf (Ty.substT j .unit u) := by
  cases u with
  | tvar k =>
      show Ty.refine (Ty.substT j .unit (.tvar k)) .tt = rf (Ty.substT j .unit (.tvar k))
      by_cases h1 : k = j
      · subst h1
        have e : Ty.substT k .unit (.tvar k) = .unit := by simp [Ty.substT]
        rw [e]; rfl
      · by_cases h2 : k > j
        · have e : Ty.substT j .unit (.tvar k) = .tvar (k - 1) := by simp [Ty.substT, h1, h2]
          rw [e]; rfl
        · have e : Ty.substT j .unit (.tvar k) = .tvar k := by simp [Ty.substT, h1, h2]
          rw [e]; rfl
  | _ => rfl

theorem skel_substT_unit : ∀ (t : Ty) (j : Nat), skel (Ty.substT j .unit t) = Ty.substT j .unit (skel t) := by
  intro t
  induction t with
  | tvar k =>
      intro j
      by_cases h1 : k = j
      · subst h1; simp [Ty.substT, skel]
      · by_cases h2 : k > j <;> simp [Ty.substT, skel, h1, h2]
  | prod a b iha ihb => intro j; simp only [Ty.substT, skel, iha, ihb]
  | sum a b iha ihb => intro j; simp only [Ty.substT, skel, iha, ihb]
  | code a b iha ihb => intro j; simp only [Ty.substT, skel, iha, ihb]
  | array i t ih => intro j; simp only [Ty.substT, skel, ih]
  | ptr μ t ih => intro j; simp only [Ty.substT, skel, ih]
  | ptrOpt μ t ih => intro j; simp only [Ty.substT, skel, ih]
  | loc μ t ih => intro j; simp only [Ty.substT, skel, ih]
  | mu t ih => intro j; simp only [Ty.substT, skel, shiftT_unit, ih]
  | tex κ t ih => intro j; simp only [Ty.substT, skel, shiftT_unit, ih]
  | iall t ih => intro j; simp only [Ty.substT, skel, shiftI_unit, ih]
  | iex t ih => intro j; simp only [Ty.substT, skel, shiftI_unit, ih]
  | refine t ψ ih => intro j; simp only [Ty.substT, skel, ih, substT_rf_unit]
  | _ => intro j; rfl

theorem shiftT_comm : ∀ (y : Ty) (c j : Nat), (y.shiftT c).shiftT (c + j + 1) = (y.shiftT (c + j)).shiftT c := by
  intro y
  induction y with
  | tvar k =>
      intro c j
      simp only [Ty.shiftT]
      by_cases h1 : k ≥ c + j
      · have h2 : k ≥ c := by omega
        simp [h1, h2, Ty.shiftT] <;> omega
      · by_cases h2 : k ≥ c
        · simp [h1, h2, Ty.shiftT] <;> omega
        · simp [h1, h2, Ty.shiftT] <;> omega
  | mu t ih => intro c j; simp only [Ty.shiftT]; have := ih (c + 1) j; rw [show c + 1 + j + 1 = c + j + 1 + 1 by omega, show c + 1 + j = c + j + 1 by omega] at this; rw [this]
  | tex κ t ih => intro c j; simp only [Ty.shiftT]; have := ih (c + 1) j; rw [show c + 1 + j + 1 = c + j + 1 + 1 by omega, show c + 1 + j = c + j + 1 by omega] at this; rw [this]
  | _ => intros; simp_all [Ty.shiftT]

theorem shiftT_shiftTN : ∀ (c j : Nat) (σ : Ty), j ≤ c → (shiftTN c σ).shiftT j = shiftTN (c + 1) σ := by
  intro c
  induction c with
  | zero => intro j σ h; have : j = 0 := by omega
            subst this; rfl
  | succ c ih =>
      intro j σ h
      cases j with
      | zero => rfl
      | succ j =>
          show (Ty.shiftT 0 (shiftTN c σ)).shiftT (j + 1) = Ty.shiftT 0 (shiftTN (c + 1) σ)
          have := shiftT_comm (shiftTN c σ) 0 j
          simp only [Nat.zero_add] at this
          rw [this, ih j σ (by omega)]

theorem substT_shiftT : ∀ (t : Ty) (c : Nat) (s : Ty), Ty.substT c s (t.shiftT c) = t := by
  intro t
  induction t with
  | tvar k =>
      intro c s
      by_cases h : k ≥ c
      · have h1 : k + 1 ≠ c := by omega
        have h2 : k + 1 > c := by omega
        simp [Ty.shiftT, Ty.substT, h, h1, h2]
      · have h1 : k ≠ c := by omega
        have h2 : ¬ k > c := by omega
        simp [Ty.shiftT, Ty.substT, h, h1, h2]
  | prod a b iha ihb => intro c s; simp only [Ty.shiftT, Ty.substT, iha, ihb]
  | sum a b iha ihb => intro c s; simp only [Ty.shiftT, Ty.substT, iha, ihb]
  | code a b iha ihb => intro c s; simp only [Ty.shiftT, Ty.substT, iha, ihb]
  | array _ t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | ptr _ t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | ptrOpt _ t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | loc _ t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | mu t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | tex _ t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | iall t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | iex t ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | refine t _ ih => intro c s; simp only [Ty.shiftT, Ty.substT, ih]
  | _ => intro c s; rfl

/-- The same on skeletons, where `substS` has no index depth. -/
theorem substT_substS_unit (τs : List Ty) : ∀ (u : Ty) (c : Nat),
    Ty.substT c .unit (substS τs (c + 1) u) = substS (.unit :: τs) c u := by
  intro u
  induction u with
  | tvar k =>
      intro c
      rcases Nat.lt_trichotomy k c with h | rfl | h
      · have h1 : k < c + 1 := by omega
        have h2 : ¬ k > c := by omega
        have h3 : k ≠ c := by omega
        simp [substS, Ty.substT, h, h1, h2, h3]
      · simp [substS, Ty.substT, shiftTN_unit]
      · obtain ⟨m, rfl⟩ : ∃ m, k = c + m + 1 := ⟨k - c - 1, by omega⟩
        have h1 : ¬ c + m + 1 < c + 1 := by omega
        have h5 : ¬ c + m + 1 < c := by omega
        have e1 : c + m + 1 - (c + 1) = m := by omega
        have e2 : c + m + 1 - c = m + 1 := by omega
        simp only [substS, h1, h5, e1, e2, if_false, List.getElem?_cons_succ, List.length_cons]
        cases hm : τs[m]? with
        | some τ => simp only [← shiftT_shiftTN c c τ (Nat.le_refl _), substT_shiftT]
        | none =>
            have hl : τs.length ≤ m := by simpa using hm
            have h6 : c + m + 1 - τs.length ≠ c := by omega
            have h7 : c + m + 1 - τs.length > c := by omega
            rw [show Ty.substT c .unit (.tvar (c + m + 1 - τs.length)) = .tvar (c + m + 1 - τs.length - 1) by
              simp [Ty.substT, h6, h7]]
            exact congrArg Ty.tvar (by omega)
  | prod a b iha ihb => intro c; simp only [substS, Ty.substT, iha, ihb]
  | sum a b iha ihb => intro c; simp only [substS, Ty.substT, iha, ihb]
  | code a b iha ihb => intro c; simp only [substS, Ty.substT, iha, ihb]
  | array i t ih => intro c; simp only [substS, Ty.substT, ih]
  | ptr μ t ih => intro c; simp only [substS, Ty.substT, ih]
  | ptrOpt μ t ih => intro c; simp only [substS, Ty.substT, ih]
  | loc μ t ih => intro c; simp only [substS, Ty.substT, ih]
  | mu t ih => intro c; simp only [substS, Ty.substT, shiftT_unit, ih]
  | tex κ t ih => intro c; simp only [substS, Ty.substT, shiftT_unit, ih]
  | iall t ih => intro c; simp only [substS, Ty.substT, shiftI_unit, ih]
  | iex t ih => intro c; simp only [substS, Ty.substT, shiftI_unit, ih]
  | refine t ψ ih => intro c; simp only [substS, substT_rf_unit, ih]
  | _ => intro c; rfl

/-- A frame variable's type after a new type binder (`Cx.pushT`): closing it
with the new argument in front is closing the old type. -/
theorem substTs_cons_shiftT (s : Ty) (σs : List Ty) : ∀ (t : Ty) (c d : Nat),
    substTs (s :: σs) c d (t.shiftT c) = substTs σs c d t := by
  intro t
  induction t with
  | tvar k =>
      intro c d
      by_cases h : k ≥ c
      · obtain ⟨m, rfl⟩ : ∃ m, k = c + m := ⟨k - c, by omega⟩
        have h1 : ¬ c + m + 1 < c := by omega
        have h2 : ¬ c + m < c := by omega
        have e1 : c + m + 1 - c = m + 1 := by omega
        have e2 : c + m - c = m := by omega
        have e : Ty.shiftT c (.tvar (c + m)) = .tvar (c + m + 1) := by simp [Ty.shiftT]
        rw [e]
        simp only [substTs, h1, h2, e1, e2, if_false, List.getElem?_cons_succ, List.length_cons]
        cases σs[m]? with
        | none => simp only [Ty.tvar.injEq]; omega
        | some σ => rfl
      · have h1 : k < c := by omega
        simp [Ty.shiftT, substTs, h, h1]
  | prod a b iha ihb => intro c d; simp only [Ty.shiftT, substTs, iha, ihb]
  | sum a b iha ihb => intro c d; simp only [Ty.shiftT, substTs, iha, ihb]
  | code a b iha ihb => intro c d; simp only [Ty.shiftT, substTs, iha, ihb]
  | array i t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | ptr μ t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | ptrOpt μ t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | loc μ t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | mu t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | tex κ t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | iall t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | iex t ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | refine t ψ ih => intro c d; simp only [Ty.shiftT, substTs, ih]
  | _ => intro c d; rfl

/-- Types without a layout have no width either (F4 makes arrays so). -/
theorem accs_none_width : ∀ t : Ty, accs t = none → (info Ty.top t).width = none := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro h
      simp only [info, Info.leaf]
      cases ha : accs a with
      | none => simp [iha ha]
      | some ua =>
          cases hb : accs b with
          | none => simp [ihb hb]
          | some ub => simp [accs, ha, hb] at h
  | sum a b _ _ => intro h; simp only [accs] at h; split at h <;> simp at h
  | refine t ψ ih => intro h; simp only [accs] at h; simp only [info]; exact ih h
  | mu t ih => intro h; simp only [accs] at h; simp only [info, top_cons]; exact ih h
  | iall t ih => intro h; simp only [accs] at h; simp only [info, top_shiftI, ih h, lowerW]; rfl
  | iex t ih =>
      intro h
      rcases accs_iex t with e | ⟨k, hr, hm⟩
      · rw [e] at h; simp only [info, top_shiftI, ih h, lowerW]; rfl
      · rw [h] at hm; simp at hm
  | tex κ t ih =>
      intro h
      rcases accs_tex κ t with e | ⟨k, hr, hm⟩
      · rw [e] at h; simp only [info, top_cons]; exact ih h
      · rw [h] at hm; simp at hm
  | array i t _ => intro _; rfl
  | tvar k => intro _; rfl
  | word r P => intro h; by_cases hg : P.ghost = true <;> simp [accs, hg] at h
  | _ => intro h; simp [accs] at h

/-- A closed width is the layout's word count. -/
theorem wc_of_width {t : Ty} {w : Idx} {k : Nat} (hw : (info Ty.top t).width = some w)
    (hk : w.closed = some k) : wc t = some k := by
  cases ha : accs t with
  | none => rw [accs_none_width t ha] at hw; simp at hw
  | some us => simp only [wc, ha, Option.map_some, accs_width t us ha w k hw hk]

/-- A package has its body's word count, coupled or not. -/
theorem wc_iex (t : Ty) : wc (.iex t) = wc t := by
  rcases accs_iex t with e | ⟨k, hr, hm⟩
  · simp only [wc, e]
  · obtain ⟨w0, hw0, hc⟩ := rawWords_iex hr
    rw [wc_of_width hw0 hc]; exact hm

theorem wc_tex (κ : Kind) (t : Ty) : wc (.tex κ t) = wc t := by
  rcases accs_tex κ t with e | ⟨k, hr, hm⟩
  · simp only [wc, e]
  · obtain ⟨w0, hw0, hc⟩ := rawWords_tex hr
    rw [wc_of_width hw0 hc]; exact hm

theorem wc_prod (a b : Ty) : wc (.prod a b) = (do pure ((← wc a) + (← wc b))) := by
  simp only [wc, accs]
  cases accs a <;> cases accs b <;> simp [nWords_append]

theorem lnorm_idem : ∀ t : Ty, lnorm (lnorm t) = lnorm t := by
  intro t; induction t <;> simp_all [lnorm, sig_idem]

theorem lnorm_rf (t : Ty) : lnorm (rf t) = lnorm t := by
  cases t <;> rfl

theorem lnorm_skel : ∀ t : Ty, lnorm (skel t) = lnorm t := by
  intro t; induction t <;> simp_all [lnorm, skel, lnorm_rf, sig_skel]

theorem wc_skel : ∀ t : Ty, wc (skel t) = wc t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [skel, wc_prod, iha, ihb]
  | sum a b _ _ =>
      have e := info_skel (.sum a b) Ty.top
      simp only [skel] at e
      simp only [skel, wc, accs, Ty.tier, e]
      by_cases hT : (info Ty.top (a.sum b)).arms.tier = Tier.wide <;> simp only [hT] <;> rfl
  | refine t ψ ih => simp only [skel, wc_rf]; simp only [wc, accs] at ih ⊢; exact ih
  | mu t ih => simp only [skel, wc, accs] at ih ⊢; exact ih
  | iall t ih => simp only [skel, wc, accs] at ih ⊢; exact ih
  | iex t ih => simp only [skel, wc_iex, ih]
  | tex κ t ih => simp only [skel, wc_tex, ih]
  | _ => rfl

theorem shp_skel : ∀ t : Ty, shp (skel t) = shp t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [skel, shp, iha, ihb]
  | iex t ih =>
      have e := wc_skel (.iex t)
      simp only [skel] at e
      simp only [skel, shp, ih, e]
  | refine t ψ ih => simp only [skel, shp_rf, shp, ih]
  | fix _ _ => rfl
  | lanes _ _ => rfl
  | sum a b _ _ =>
      have e := wc_skel (.sum a b)
      have el := lnorm_skel (.sum a b)
      simp only [skel] at e el ⊢; simp only [shp, e, el]
  | code a b _ _ => simp only [skel, shp, sig_skel]
  | array i t _ => have e := wc_skel (.array i t); simp only [skel] at e ⊢; simp only [shp, e]
  | ptr μ t _ => have e := wc_skel (.ptr μ t); simp only [skel] at e ⊢; simp only [shp, e]
  | ptrOpt μ t _ => have e := wc_skel (.ptrOpt μ t); simp only [skel] at e ⊢; simp only [shp, e]
  | loc μ t _ => have e := wc_skel (.loc μ t); simp only [skel] at e ⊢; simp only [shp, e]
  | mu t ih => simp only [skel, shp, ih]
  | tex κ t ih => have e := wc_skel (.tex κ t); simp only [skel] at e ⊢; simp only [shp, e, ih]
  | iall t ih => simp only [skel, shp, ih]
  | _ => rfl

theorem shp_of_skel {t u : Ty} (h : skel t = skel u) : shp t = shp u := by
  rw [← shp_skel t, h, shp_skel]

theorem wc_of_skel {t u : Ty} (h : skel t = skel u) : wc t = wc u := by
  rw [← wc_skel t, h, wc_skel]

/-- Index shifts do not move a closed type's skeleton (`push`). -/
theorem skel_close_shiftI (σs : List Ty) (t : Ty) (c : Nat) :
    skel (close σs (t.shiftI c)) = skel (close σs t) := by
  simp only [close, skel_substTs, skel_shiftI]

/-- Nor do index instantiation and the depth a substitution runs at (`pack`,
`unpack`). -/
theorem skel_subst_instT (σs : List Ty) (us : List Idx) (t : Ty) (c d d' e : Nat) :
    skel (substTs σs c d (instT us e t)) = skel (substTs σs c d' t) := by
  simp only [skel_substTs, skel_instT]

/-- Type equality is skeleton equality (and more). -/
theorem skel_tyEq {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) : skel t = skel u := by
  induction h with
  | refl => rfl
  | intS => rfl
  | prod _ _ ih1 ih2 => simp only [skel, ih1, ih2]
  | sum _ _ ih1 ih2 => simp only [skel, ih1, ih2]
  | code _ _ ih1 ih2 => simp only [skel, ih1, ih2]
  | array _ _ ih => simp only [skel, ih]
  | ptr hm _ ih => cases hm <;> simp only [skel, skelM, ih]
  | ptrOpt hm _ ih => cases hm <;> simp only [skel, skelM, ih]
  | loc hm _ ih => cases hm <;> simp only [skel, skelM, ih]
  | word => rfl
  | word2 => rfl
  | tok2 => rfl
  | epair => rfl
  | tokE => rfl
  | tokNone => rfl
  | tokSome => rfl
  | share => rfl
  | cap => rfl
  | mu _ ih => simp only [skel, ih]
  | tex _ ih => simp only [skel, ih]
  | iall _ ih => simp only [skel, ih]
  | iex _ ih => simp only [skel, ih]
  | refine _ ih => simp only [skel, ih]
  | refineIni _ _ ih => simp only [skel, ih]

/-- What a sum's tier reads from an arm: everything but the payload-free count. -/
def InfoEqU (i j : Info) : Prop :=
  i.width = j.width ∧ i.arms.ptrs = j.arms.ptrs ∧ i.arms.wide = j.arms.wide ∧ i.arms.maxW = j.arms.maxW

theorem InfoEqU.refl (i : Info) : InfoEqU i i := ⟨rfl, rfl, rfl, rfl⟩

theorem InfoEqU.tier {i j : Info} (h : InfoEqU i j) : i.arms.tier = j.arms.tier := by
  obtain ⟨-, hp, hw, hm⟩ := h
  unfold Arms.tier Arms.slots; rw [hp, hw, hm]

/-- `info`'s sum case, as a function of the arms' infos. -/
def sumI (A B : Info) : Info :=
  let arms := A.arms.combine B.arms
  if arms.maxW.isNone then ⟨none, arms⟩ else
  match arms.tier with
  | .wide => ⟨some (.lit 2), arms⟩
  | _     => ⟨some (.lit 1), arms⟩

theorem info_sum (ρ : Ctx) (a b : Ty) : info ρ (.sum a b) = sumI (info ρ a) (info ρ b) := rfl

theorem InfoEqU.sum {A B A' B' : Info} (h1 : InfoEqU A A') (h2 : InfoEqU B B') :
    InfoEqU (sumI A B) (sumI A' B') := by
  obtain ⟨-, pa, wa, ma⟩ := h1
  obtain ⟨-, pb, wb, mb⟩ := h2
  have hp : (A.arms.combine B.arms).ptrs = (A'.arms.combine B'.arms).ptrs := by
    simp only [Arms.combine, pa, pb]
  have hw : (A.arms.combine B.arms).wide = (A'.arms.combine B'.arms).wide := by
    simp only [Arms.combine, wa, wb]
  have hm : (A.arms.combine B.arms).maxW = (A'.arms.combine B'.arms).maxW := by
    simp only [Arms.combine, ma, mb]
  have ht : (A.arms.combine B.arms).tier = (A'.arms.combine B'.arms).tier := by
    unfold Arms.tier Arms.slots; rw [hp, hw, hm]
  unfold sumI
  dsimp only
  rw [hm, ht]
  by_cases hc : (A'.arms.combine B'.arms).maxW.isNone = true
  · simp only [hc, ite_true]; exact ⟨rfl, hp, hw, hm⟩
  · simp only [hc]
    cases hT : (A'.arms.combine B'.arms).tier <;> exact ⟨rfl, hp, hw, hm⟩

/-- At a context that knows no variable's width (`Ty.top`, under any binders):
`lnorm` sends every variable to `tvar 0` (24e), which such a context cannot
tell apart. -/
theorem info_lnorm : ∀ (t : Ty) (ρ : Ctx), (∀ k, ρ k = none) →
    InfoEqU (info ρ (lnorm t)) (info ρ t) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ρ hρ; simp only [lnorm, info, (iha ρ hρ).1, (ihb ρ hρ).1]; exact InfoEqU.refl _
  | sum a b iha ihb => intro ρ hρ; simp only [lnorm, info_sum]; exact InfoEqU.sum (iha ρ hρ) (ihb ρ hρ)
  | mu t ih =>
      intro ρ hρ; simp only [lnorm, info]
      exact ih _ (fun k => by cases k <;> simp [Ctx.cons, hρ])
  | tex κ t ih =>
      intro ρ hρ; simp only [lnorm, info]
      exact ih _ (fun k => by cases k <;> simp [Ctx.cons, hρ])
  | iall t ih =>
      intro ρ hρ; obtain ⟨h1, h2, h3, h4⟩ := ih ρ.shiftI (fun k => by simp [Ctx.shiftI, hρ])
      simp only [lnorm, info]; exact ⟨by rw [h1], h2, h3, h4⟩
  | iex t ih =>
      intro ρ hρ; obtain ⟨h1, h2, h3, h4⟩ := ih ρ.shiftI (fun k => by simp [Ctx.shiftI, hρ])
      simp only [lnorm, info]; exact ⟨by rw [h1], h2, h3, h4⟩
  | refine t ψ ih => intro ρ hρ; simp only [lnorm, info]; exact ih ρ hρ
  | tvar k => intro ρ hρ; simp only [lnorm, info, hρ]; exact InfoEqU.refl _
  | _ => intro ρ _; exact ⟨rfl, rfl, rfl, rfl⟩

theorem tier_lnorm (t : Ty) : (lnorm t).tier = t.tier := (info_lnorm t Ty.top (fun _ => rfl)).tier

theorem width_lnorm (t : Ty) : (lnorm t).width = t.width := (info_lnorm t Ty.top (fun _ => rfl)).1

theorem rawWords_lnorm (t : Ty) : (lnorm t).rawWords = t.rawWords := by
  simp only [Ty.rawWords, width_lnorm]

theorem wc_lnorm : ∀ t : Ty, wc (lnorm t) = wc t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [lnorm, wc_prod, iha, ihb]
  | sum a b _ _ =>
      have e := tier_lnorm (.sum a b)
      simp only [lnorm] at e
      simp only [lnorm, wc, accs, e]
  | refine t ψ ih => simp only [lnorm]; simp only [wc, accs] at ih ⊢; exact ih
  | mu t ih => simp only [lnorm, wc, accs] at ih ⊢; exact ih
  | iall t ih => simp only [lnorm, wc, accs] at ih ⊢; exact ih
  | iex t ih => simp only [lnorm, wc_iex, ih]
  | tex κ t ih => simp only [lnorm, wc_tex, ih]
  | word r P => by_cases hg : P.ghost = true <;> simp [lnorm, wc, accs, hg]
  | _ => rfl

theorem lnorm_sub {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat),
    lnorm (substTs σs c d σ) = lnorm (substTs σs c d τ) := by
  induction h with
  | eq h =>
      intro σs c d
      rw [← lnorm_skel, skel_subst_eq (skel_tyEq h) σs c d d, lnorm_skel]
  | intS => intro σs c d; rfl
  | refine _ ih => intro σs c d; simpa only [substTs, lnorm] using ih σs c d
  | iniWeak h _ =>
      intro σs c d
      simp only [substTs, lnorm]
      rw [← lnorm_skel, skel_subst_eq (skel_tyEq h) σs c d d, lnorm_skel]
  | nonNull => intro σs c d; rfl
  | prod _ _ iha ihb => intro σs c d; simp only [substTs, lnorm, iha σs c d, ihb σs c d]
  | sum _ _ iha ihb => intro σs c d; simp only [substTs, lnorm, iha σs c d, ihb σs c d]
  | cap => intro σs c d; rfl

/-- **Subsumption keeps layouts** (after any type substitution): every `SubS`
case is representation-preserving, and `Ptr <: Ptr?` inside a sum does not
move its tier (F3). -/
theorem info_sub {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat),
    InfoEqU (info Ty.top (substTs σs c d σ)) (info Ty.top (substTs σs c d τ)) := by
  induction h with
  | eq h =>
      intro σs c d
      rw [← info_skel _ Ty.top, skel_subst_eq (skel_tyEq h) σs c d d, info_skel]
      exact InfoEqU.refl _
  | intS => intro σs c d; exact InfoEqU.refl _
  | refine _ ih => intro σs c d; simpa only [substTs, info] using ih σs c d
  | iniWeak h _ =>
      intro σs c d
      simp only [substTs, info]
      rw [← info_skel _ Ty.top, skel_subst_eq (skel_tyEq h) σs c d d, info_skel]
      exact InfoEqU.refl _
  | nonNull => intro σs c d; exact ⟨rfl, rfl, rfl, rfl⟩
  | prod _ _ iha ihb =>
      intro σs c d
      simp only [substTs, info, (iha σs c d).1, (ihb σs c d).1]
      exact InfoEqU.refl _
  | sum _ _ iha ihb =>
      intro σs c d
      simp only [substTs, info_sum]
      exact InfoEqU.sum (iha σs c d) (ihb σs c d)
  | cap => intro σs c d; exact InfoEqU.refl _

/-- **Subsumption keeps shapes** (after any type substitution). -/
theorem shp_sub {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat),
    shp (substTs σs c d σ) = shp (substTs σs c d τ) := by
  induction h with
  | eq h => intro σs c d; exact shp_of_skel (skel_subst_eq (skel_tyEq h) σs c d d)
  | intS => intro σs c d; rfl
  | refine _ ih => intro σs c d; simpa only [substTs, shp] using ih σs c d
  | iniWeak h _ =>
      intro σs c d
      simp only [substTs, shp]
      exact shp_of_skel (skel_subst_eq (skel_tyEq h) σs c d d)
  | nonNull => intro σs c d; rfl
  | prod _ _ iha ihb => intro σs c d; simp only [substTs, shp, iha σs c d, ihb σs c d]
  | sum ha hb _ _ =>
      intro σs c d
      have e := (info_sub (SubS.sum ha hb) σs c d).tier
      have el := lnorm_sub (SubS.sum ha hb) σs c d
      simp only [substTs] at e el ⊢
      simp only [shp, el]
      congr 1
      simp only [wc, accs, Ty.tier, e]
      rfl
  | cap => intro σs c d; rfl

theorem wc_sub {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) (σs : List Ty) (c d : Nat) :
    wc (substTs σs c d σ) = wc (substTs σs c d τ) := by
  rw [← shp_wc, ← shp_wc, shp_sub h]

/-! ### Arms, as the encoder sees them -/

/-- What `encodeArm`/`decodeArm` read from an arm, in the order `Ptr ≤ Ptr?`. -/
def ArmLe (a b : Ty) : Prop :=
  (armK a = armK b ∨ (armK a = .ptr ∧ armK b = .opt)) ∧ a.rawWords = b.rawWords

theorem ArmLe.refl (a : Ty) : ArmLe a a := ⟨Or.inl rfl, rfl⟩

theorem ArmLe.ptrish {a b : Ty} (h : ArmLe a b) : isPtrish a = isPtrish b := by
  rcases h.1 with e | ⟨e1, e2⟩
  · simp [isPtrish, e]
  · simp [isPtrish, e1, e2]

inductive ArmsLeR (R : Ty → Ty → Prop) : List Ty → List Ty → Prop
  | nil : ArmsLeR R [] []
  | cons {a b : Ty} {as bs : List Ty} : R a b → ArmsLeR R as bs → ArmsLeR R (a :: as) (b :: bs)

abbrev ArmsLe := ArmsLeR ArmLe

theorem armK_of_arms {a b : Ty} (h : (info Ty.top a).arms = (info Ty.top b).arms) : armK a = armK b := by
  unfold armK; rw [h]

theorem ArmLe.of_arms {a b : Ty} (h : (info Ty.top a).arms = (info Ty.top b).arms)
    (hw : a.rawWords = b.rawWords) : ArmLe a b := ⟨Or.inl (armK_of_arms h), hw⟩

theorem armsOf_lnorm : ∀ t : Ty, armsOf (lnorm t) = (armsOf t).map lnorm := by
  intro t; induction t <;> simp_all [lnorm, armsOf]

theorem armLe_lnorm : ∀ t : Ty, ∀ a ∈ armsOf t, ArmLe a (lnorm a) := by
  intro t
  induction t with
  | sum a b iha ihb =>
      intro x hx; simp only [armsOf, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx
  | void => intro x hx; simp [armsOf] at hx
  | mu t ih => intro x hx; exact ih x hx
  | tex κ t ih => intro x hx; exact ih x hx
  | iall t ih => intro x hx; exact ih x hx
  | iex t ih => intro x hx; exact ih x hx
  | refine t ψ ih => intro x hx; exact ih x hx
  | prod a b _ _ =>
      intro x hx; simp only [armsOf, List.mem_singleton] at hx; subst hx
      have e := (info_lnorm (.prod a b) Ty.top (fun _ => rfl)).1
      refine ArmLe.of_arms ?_ (rawWords_lnorm _).symm
      simp only [lnorm, info, Info.leaf] at e ⊢; rw [e]
  | ptr μ t _ =>
      intro x hx; simp only [armsOf, List.mem_singleton] at hx; subst hx
      refine ⟨Or.inr ⟨?_, ?_⟩, (rawWords_lnorm _).symm⟩ <;> simp [armK, info, lnorm, Arms.ptrArm, Arms.optArm]
  | _ =>
      intro x hx; simp only [armsOf, List.mem_singleton] at hx; subst hx
      exact ArmLe.of_arms rfl (rawWords_lnorm _).symm

theorem forall2_map {R : Ty → Ty → Prop} {f : Ty → Ty} :
    ∀ (l : List Ty), (∀ a ∈ l, R a (f a)) → ArmsLeR R l (l.map f)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall2_map l (fun x hx => h x (by simp [hx])))

theorem arms_lnorm (t : Ty) : ArmsLe (armsOf t) (armsOf (lnorm t)) := by
  rw [armsOf_lnorm]; exact forall2_map _ (armLe_lnorm t)

theorem ptrIdx_mono {as bs : List Ty} (h : ArmsLe as bs) : ∀ n,
    ((enumFrom as n).filter (fun p => isPtrish p.2)).map Prod.fst =
    ((enumFrom bs n).filter (fun p => isPtrish p.2)).map Prod.fst := by
  induction h with
  | nil => intro n; rfl
  | cons hab _ ih =>
      intro n
      simp only [enumFrom, List.filter_cons, hab.ptrish]
      split <;> simp [ih]

theorem slot_mono {as bs : List Ty} (h : ArmsLe as bs) : ∀ j,
    ((as.take j).filter isPtrish).length = ((bs.take j).filter isPtrish).length := by
  induction h with
  | nil => intro j; simp
  | cons hab _ ih =>
      intro j; cases j with
      | zero => simp
      | succ j => simp only [List.take_succ_cons, List.filter_cons, hab.ptrish]; split <;> simp [ih]

theorem get_mono {as bs : List Ty} (h : ArmsLe as bs) {j : Nat} {a : Ty}
    (ha : as[j]? = some a) : ∃ b, bs[j]? = some b ∧ ArmLe a b := by
  induction h generalizing j with
  | nil => simp at ha
  | cons hab _ ih =>
      cases j with
      | zero => simp at ha; subst ha; exact ⟨_, rfl, hab⟩
      | succ j => simp at ha; exact ih ha

/-- **Decoding is monotone** in the arms: what decodes at `Ptr` decodes the same at `Ptr?`. -/
theorem decodeArm_mono {tr : Tier} {as bs : List Ty} {ws : List Word} {x : Nat × List Word}
    (h : ArmsLe as bs) (hd : decodeArm tr as ws = some x) : decodeArm tr bs ws = some x := by
  cases tr with
  | boxed => simp [decodeArm] at hd
  | niche =>
      match ws, hd with
      | [w], hd =>
          simp only [decodeArm] at hd ⊢
          cases hw : w.val with
          | loc a g =>
              rw [hw] at hd
              have e := congrArg (fun l => l[g]?) (ptrIdx_mono h 0)
              simp only [List.getElem?_map] at e
              cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
              | none => simp [h1, bind, Option.bind] at hd
              | some pr =>
                  cases h2 : ((enumFrom bs 0).filter (fun p => isPtrish p.2))[g]? with
                  | none => simp [h1, h2] at e
                  | some pr' =>
                      simp [h1, h2] at e
                      simp only [h1, bind, Option.bind] at hd
                      simp only [h2, bind, Option.bind]
                      rw [← e]; exact hd
          | num j =>
              rw [hw] at hd
              cases h1 : as[j]? with
              | none => simp [h1, bind, Option.bind] at hd
              | some a =>
                  obtain ⟨b, h2, hab⟩ := get_mono h h1
                  simp only [h1, bind, Option.bind] at hd
                  simp only [h2, bind, Option.bind]
                  rcases hab.1 with e | ⟨e1, e2⟩
                  · rw [← e]; exact hd
                  · rw [e1] at hd; simp at hd
          | _ => rw [hw] at hd; simp at hd
      | [], hd => simp [decodeArm] at hd
      | _ :: _ :: _, hd => simp [decodeArm] at hd
  | wide =>
      match ws, hd with
      | [t, w], hd =>
          simp only [decodeArm] at hd ⊢
          cases ht : t.val with
          | num j =>
              rw [ht] at hd
              cases h1 : as[j]? with
              | none => simp [h1, bind, Option.bind] at hd
              | some a =>
                  obtain ⟨b, h2, hab⟩ := get_mono h h1
                  simp only [h1, bind, Option.bind] at hd
                  simp only [h2, bind, Option.bind, ← hab.2]
                  exact hd
          | _ => rw [ht] at hd; simp at hd
      | [], hd => simp [decodeArm] at hd
      | [_], hd => simp [decodeArm] at hd
      | _ :: _ :: _ :: _, hd => simp [decodeArm] at hd

/-- **Encoding is monotone** in the arms. -/
theorem encodeArm_mono {tr : Tier} {as bs : List Ty} {j : Nat} {p q : List Word}
    (h : ArmsLe as bs) (he : encodeArm tr as j p = some q) : encodeArm tr bs j p = some q := by
  cases tr with
  | niche =>
      simp only [encodeArm, bind, Option.bind] at he ⊢
      cases h1 : as[j]? with
      | none => simp [h1] at he
      | some a =>
          obtain ⟨b, h2, hab⟩ := get_mono h h1
          simp only [h1] at he
          simp only [h2, ← slot_mono h j]
          rcases hab.1 with e | ⟨e1, e2⟩
          · rw [← e]; exact he
          · rw [e1] at he; rw [e2]
            match p, he with
            | [w], he =>
                simp only at he ⊢
                split at he
                · exact he
                · simp at he
                · simp at he
  | wide => exact he
  | boxed => simp [encodeArm] at he

/-! ### Arms are atoms -/

/-- What `armsOf` returns: no sum, no wrapper, not `Void`. -/
def Atom : Ty → Prop
  | .sum _ _ | .void | .refine _ _ | .iall _ | .iex _ | .mu _ | .tex _ _ => False
  | _ => True

theorem atom_of_mem : ∀ (t a : Ty), a ∈ armsOf t → Atom a := by
  intro t
  induction t with
  | sum a b iha ihb =>
      intro x hx; simp only [armsOf, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx
  | void => intro x hx; simp [armsOf] at hx
  | mu t ih => intro x hx; exact ih x hx
  | tex κ t ih => intro x hx; exact ih x hx
  | iall t ih => intro x hx; exact ih x hx
  | iex t ih => intro x hx; exact ih x hx
  | refine t ψ ih => intro x hx; exact ih x hx
  | _ => intro x hx; simp only [armsOf, List.mem_singleton] at hx; subst hx; trivial

theorem atom_arms : ∀ a : Ty, Atom a →
    (info Ty.top a).arms = Arms.leaf (info Ty.top a).width ∨
    (info Ty.top a).arms = Arms.ptrArm ∨ (info Ty.top a).arms = Arms.optArm := by
  intro a ha
  cases a <;> simp only [Atom] at ha <;> simp [info, Info.leaf]

theorem leaf_maxW (w : Option Idx) : (Arms.leaf w).maxW = w.bind Idx.closed := by
  unfold Arms.leaf; split <;> simp_all

theorem atom_maxW {a : Ty} (ha : Atom a) : (info Ty.top a).arms.maxW = a.rawWords := by
  cases a <;> simp only [Atom] at ha <;>
    simp [info, Info.leaf, leaf_maxW, Ty.rawWords, Ty.width, Arms.ptrArm, Arms.optArm, Idx.closed]

theorem atom_nil {a : Ty} (ha : Atom a) (h : armK a = .nil) : a.rawWords = some 0 := by
  have hm := atom_maxW ha
  unfold armK at h
  rcases atom_arms a ha with e | e | e
  · rw [e] at h hm
    unfold Arms.leaf at h hm
    split at h <;> simp_all [Arms.ptrArm, Arms.optArm]
  · rw [e] at h; simp at h
  · rw [e] at h; simp [Arms.ptrArm, Arms.optArm] at h

theorem atom_ptrish {a : Ty} (ha : Atom a) (h : isPtrish a = true) : a.rawWords = some 1 := by
  have hm := atom_maxW ha
  unfold isPtrish armK at h
  rcases atom_arms a ha with e | e | e
  · rw [e] at h hm
    unfold Arms.leaf at h hm
    split at h <;> simp_all [Arms.ptrArm, Arms.optArm]
  · rw [e] at hm; simpa [Arms.ptrArm] using hm.symm
  · rw [e] at hm; simpa [Arms.optArm] using hm.symm

theorem atom_wide {a : Ty} (ha : Atom a) (h : armK a = .wide) : (info Ty.top a).arms.wide = 1 := by
  unfold armK at h
  rcases atom_arms a ha with e | e | e
  · rw [e] at h ⊢
    unfold Arms.leaf at h ⊢
    split at h <;> simp_all [Arms.ptrArm, Arms.optArm]
  · rw [e] at h; simp at h
  · rw [e] at h; simp [Arms.ptrArm, Arms.optArm] at h

/-! ### A sum's arms, from its flattened arms -/

def armsF (l : List Ty) : Arms := l.foldr (fun a acc => (info Ty.top a).arms.combine acc) Arms.empty

theorem combine_empty (A : Arms) : A.combine Arms.empty = A := by
  cases A with
  | mk p u w m => cases m <;> simp [Arms.combine, Arms.empty, bind, Option.bind]

theorem combine_assoc (A B C : Arms) : (A.combine B).combine C = A.combine (B.combine C) := by
  cases A; cases B; cases C
  rename_i m1 _ _ _ m2 _ _ _ m3
  simp only [Arms.combine, Arms.mk.injEq]
  refine ⟨by omega, by omega, by omega, ?_⟩
  cases m1 <;> cases m2 <;> cases m3 <;> simp [bind, Option.bind, Nat.max_assoc]

@[simp] theorem armsF_nil : armsF [] = Arms.empty := rfl
@[simp] theorem armsF_cons (a : Ty) (l : List Ty) :
    armsF (a :: l) = (info Ty.top a).arms.combine (armsF l) := rfl

theorem empty_combine (A : Arms) : Arms.empty.combine A = A := by
  cases A with
  | mk p u w m => cases m <;> simp [Arms.combine, Arms.empty, bind, Option.bind]

theorem armsF_append (l m : List Ty) : armsF (l ++ m) = (armsF l).combine (armsF m) := by
  induction l with
  | nil => simp [empty_combine]
  | cons a l ih => simp only [List.cons_append, armsF_cons, ih, combine_assoc]

theorem arms_info : ∀ t : Ty, (info Ty.top t).arms = armsF (armsOf t) := by
  intro t
  induction t with
  | sum a b iha ihb => simp only [info_sum, sumI, armsOf, armsF_append, ← iha, ← ihb]; split <;> (try split) <;> rfl
  | void => rfl
  | mu t ih => simp only [info, top_cons, armsOf]; exact ih
  | tex κ t ih => simp only [info, top_cons, armsOf]; exact ih
  | iall t ih => simp only [info, top_shiftI, armsOf]; exact ih
  | iex t ih => simp only [info, top_shiftI, armsOf]; exact ih
  | refine t ψ ih => simp only [info, armsOf]; exact ih
  | _ => simp [armsOf, armsF, combine_empty]

theorem armsF_wide : ∀ (l : List Ty), (armsF l).wide = 0 → ∀ a ∈ l, (info Ty.top a).arms.wide = 0 := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
      intro h a ha
      simp only [armsF_cons, Arms.combine] at h
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · exact ih (by omega) a ha

theorem armsF_maxW : ∀ (l : List Ty) (k : Nat), (armsF l).maxW = some k → ∀ a ∈ l,
    ∃ k', (info Ty.top a).arms.maxW = some k' ∧ k' ≤ k := by
  intro l
  induction l with
  | nil => intro _ _ a ha; simp at ha
  | cons x l ih =>
      intro k h a ha
      simp only [armsF_cons, Arms.combine] at h
      cases hx : (info Ty.top x).arms.maxW with
      | none => simp [hx, bind, Option.bind] at h
      | some kx =>
          cases hl : (armsF l).maxW with
          | none => simp [hx, hl, bind, Option.bind] at h
          | some kl =>
              simp [hx, hl, bind, Option.bind] at h
              subst h
              simp only [List.mem_cons] at ha
              rcases ha with rfl | ha
              · exact ⟨kx, hx, Nat.le_max_left _ _⟩
              · obtain ⟨k', h1, h2⟩ := ih kl hl a ha
                exact ⟨k', h1, Nat.le_trans h2 (Nat.le_max_right _ _)⟩

/-- In a non-boxed sum every arm has a closed width of at most one word, and in
a niche sum no arm is wide. -/
theorem arm_of_tier {t a : Ty} (ht : t.tier ≠ .boxed) (ha : a ∈ armsOf t) :
    (∃ k, a.rawWords = some k ∧ k ≤ 1) ∧ (t.tier = .niche → armK a ≠ .wide) := by
  have hA := atom_of_mem t a ha
  unfold Ty.tier at ht ⊢
  rw [arms_info] at ht ⊢
  unfold Arms.tier at ht ⊢
  refine ⟨?_, ?_⟩
  · by_cases hn : (armsF (armsOf t)).wide = 0 ∧ (armsF (armsOf t)).slots ≤ tagSlots
    · have hw := armsF_wide _ hn.1 a ha
      rw [← atom_maxW hA]
      rcases atom_arms a hA with e | e | e
      · rw [e] at hw ⊢
        unfold Arms.leaf at hw ⊢
        split at hw <;> simp_all
      · rw [e]; exact ⟨1, rfl, Nat.le_refl _⟩
      · rw [e]; exact ⟨1, rfl, Nat.le_refl _⟩
    · simp only [hn, ite_false] at ht
      split at ht
      · rename_i hm
        cases hk : (armsF (armsOf t)).maxW with
        | none => simp [hk] at hm
        | some k =>
            simp [hk] at hm
            obtain ⟨k', h1, h2⟩ := armsF_maxW _ k hk a ha
            rw [← atom_maxW hA]; exact ⟨k', h1, by omega⟩
      · exact absurd rfl ht
  · intro hn hw
    split at hn
    · rename_i hc
      have := armsF_wide _ hc.1 a ha
      rw [atom_wide hA hw] at this; simp at this
    · split at hn <;> simp at hn

/-! ### Components of a non-boxed sum are non-boxed -/

theorem tier_combine {A B : Arms} (h : (A.combine B).tier ≠ .boxed) :
    A.tier ≠ .boxed ∧ B.tier ≠ .boxed := by
  unfold Arms.tier Arms.slots tagSlots at h ⊢
  split at h
  · rename_i hn
    simp only [Arms.combine] at hn
    constructor
    · rw [if_pos (by omega)]; simp
    · rw [if_pos (by omega)]; simp
  · split at h
    · rename_i hm
      simp only [Arms.combine] at hm
      cases ha : A.maxW with
      | none => simp [ha, bind, Option.bind] at hm
      | some x =>
          cases hb : B.maxW with
          | none => simp [ha, hb, bind, Option.bind] at hm
          | some y =>
              simp [ha, hb, bind, Option.bind] at hm
              constructor
              · split
                · simp
                · rw [if_pos (by simp; omega)]; simp
              · split
                · simp
                · rw [if_pos (by simp; omega)]; simp
    · exact absurd rfl h

theorem tier_sum {a b : Ty} (h : (Ty.sum a b).tier ≠ .boxed) : a.tier ≠ .boxed ∧ b.tier ≠ .boxed := by
  have e : (info Ty.top (.sum a b)).arms = (info Ty.top a).arms.combine (info Ty.top b).arms := by
    simp only [info_sum, sumI]; split <;> (try split) <;> rfl
  unfold Ty.tier at h ⊢; rw [e] at h; exact tier_combine h

/-! ### Values: encoding and decoding read only values -/

theorem sumHead_lnorm : ∀ t : Ty, sumHead (lnorm t) = sumHead t := by
  intro t; induction t <;> simp_all [lnorm, sumHead]

/-- Machine agreement: what the machine builds at a runtime type, the layout
normal form builds too. -/
theorem ofArm_lnorm {t : Ty} {j : Nat} {p q : List Word} (h : ofArm t j p = some q) :
    ofArm (lnorm t) j p = some q := by
  unfold ofArm at h ⊢
  rw [sumHead_lnorm, tier_lnorm]
  split at h
  · rename_i hs; rw [if_pos hs]; exact encodeArm_mono (arms_lnorm t) h
  · rename_i hs; rw [if_neg hs]; exact h

theorem asArm_lnorm {t : Ty} {ws : List Word} {x : Nat × List Word} (h : asArm t ws = some x) :
    asArm (lnorm t) ws = some x := by
  unfold asArm at h ⊢
  rw [sumHead_lnorm, tier_lnorm]
  split at h
  · rename_i hs; rw [if_pos hs]; exact decodeArm_mono (arms_lnorm t) h
  · rename_i hs; rw [if_neg hs]; exact h

/-! ### Payloads and round trips -/

theorem PayOK_vals {a : Ty} {p p' : List Word} (e : VEq p p') (h : PayOK a p) : PayOK a p' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hl : p.length = p'.length := by simpa using congrArg List.length e
  refine ⟨hl ▸ h1, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨w, adr, rfl, hw⟩ := h2 hk
    obtain ⟨w', rfl, ew⟩ := veq_one e
    exact ⟨w', adr, rfl, ew.trans hw⟩
  · obtain ⟨w, rfl, hw⟩ := h3 hk
    obtain ⟨w', rfl, ew⟩ := veq_one e
    exact ⟨w', rfl, by rw [ew]; exact hw⟩

theorem PayOK_mono {a b : Ty} {p : List Word} (hab : ArmLe a b) (h : PayOK a p) : PayOK b p := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hab.2 ▸ h1, fun hk => ?_, fun hk => ?_⟩
  · rcases hab.1 with e | ⟨_, e2⟩
    · exact h2 (e.trans hk)
    · rw [e2] at hk; simp at hk
  · rcases hab.1 with e | ⟨e1, _⟩
    · exact h3 (e.trans hk)
    · obtain ⟨w, adr, rfl, hw⟩ := h2 e1
      exact ⟨w, rfl, Or.inr ⟨adr, hw⟩⟩

theorem getElem?_mem {l : List Ty} {j : Nat} {a : Ty} (h : l[j]? = some a) : a ∈ l := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hj, rfl⟩ := h
  exact List.getElem_mem hj

/-- **Encoding succeeds** on a fitting payload at a non-boxed tier. -/
theorem encode_ok {t a : Ty} {j : Nat} {p : List Word} (ht : t.tier ≠ .boxed)
    (ha : (armsOf t)[j]? = some a) (hp : PayOK a p) :
    ∃ q, encodeArm t.tier (armsOf t) j p = some q := by
  have hm := getElem?_mem ha
  obtain ⟨⟨k, hk, hk1⟩, hn⟩ := arm_of_tier ht hm
  have hA := atom_of_mem t a hm
  obtain ⟨hl, hptr, hopt⟩ := hp
  cases htr : t.tier with
  | boxed => exact absurd htr ht
  | wide =>
      rw [hk] at hl; simp at hl
      match p, hl with
      | [], _ => exact ⟨_, rfl⟩
      | [w], _ => exact ⟨_, rfl⟩
      | _ :: _ :: _, hl => simp at hl; omega
  | niche =>
      simp only [encodeArm, bind, Option.bind, ha]
      cases hkd : armK a with
      | ptr =>
          obtain ⟨w, adr, rfl, hw⟩ := hptr hkd
          simp [hw]
      | opt =>
          obtain ⟨w, rfl, hw⟩ := hopt hkd
          rcases hw with hw | ⟨adr, hw⟩ <;> simp [hw, hkd]
      | nil =>
          have := atom_nil hA hkd
          rw [this] at hl; simp at hl
          have hl := hl.symm; rw [List.length_eq_zero_iff] at hl; subst hl; simp
      | wide => exact absurd hkd (hn htr)

theorem ptr_index : ∀ (as : List Ty) (n j : Nat) (a : Ty), as[j]? = some a → isPtrish a = true →
    ((enumFrom as n).filter (fun p => isPtrish p.2))[((as.take j).filter isPtrish).length]? =
      some (n + j, a) := by
  intro as
  induction as with
  | nil => intro n j a h; simp at h
  | cons x as ih =>
      intro n j a h hp
      cases j with
      | zero =>
          simp at h; subst h
          simp [enumFrom, List.filter_cons, hp]
      | succ j =>
          simp at h
          have := ih (n + 1) j a h hp
          simp only [enumFrom, List.filter_cons, List.take_succ_cons]
          by_cases hx : isPtrish x = true
          · simp only [hx, ite_true, List.length_cons, List.getElem?_cons_succ]
            rw [this]; congr 2; omega
          · simp only [hx]; simp only [Bool.false_eq_true, ite_false]
            rw [this]; congr 2; omega

/-- **Round trip**: decoding an encoded fitting payload gives back the arm and
the payload's values. -/
theorem roundtrip {t a : Ty} {j : Nat} {p q : List Word} (ht : t.tier ≠ .boxed)
    (ha : (armsOf t)[j]? = some a) (hp : PayOK a p) (he : encodeArm t.tier (armsOf t) j p = some q) :
    ∃ p', decodeArm t.tier (armsOf t) q = some (j, p') ∧ VEq p p' := by
  have hm := getElem?_mem ha
  obtain ⟨⟨k, hk, hk1⟩, hn⟩ := arm_of_tier ht hm
  have hA := atom_of_mem t a hm
  obtain ⟨hl, hptr, hopt⟩ := hp
  cases htr : t.tier with
  | boxed => exact absurd htr ht
  | wide =>
      rw [htr] at he
      rw [hk] at hl; simp at hl
      match p, hl, he with
      | [], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[], ?_, rfl⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | [w], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[w], ?_, rfl⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | _ :: _ :: _, hl, _ => simp at hl; omega
  | niche =>
      rw [htr] at he
      simp only [encodeArm, bind, Option.bind, ha] at he
      cases hkd : armK a with
      | ptr =>
          obtain ⟨w, adr, rfl, hw⟩ := hptr hkd
          simp [hkd, hw] at he; subst he
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          refine ⟨[{ w with val := .loc adr 0 }], ?_, by simp [VEq, hw]⟩
          simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | opt =>
          obtain ⟨w, rfl, hw⟩ := hopt hkd
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          rcases hw with hw | ⟨adr, hw⟩
          · simp [hkd, hw] at he; subst he
            refine ⟨[cst .null], ?_, by simp [VEq, hw]⟩
            simp [decodeArm, bind, Option.bind, ha, hkd, pure]
          · simp [hkd, hw] at he; subst he
            refine ⟨[{ w with val := .loc adr 0 }], ?_, by simp [VEq, hw]⟩
            simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | nil =>
          have := atom_nil hA hkd
          rw [this] at hl; simp at hl
          have hl := hl.symm; rw [List.length_eq_zero_iff] at hl; subst hl
          simp [hkd] at he; subst he
          refine ⟨[], ?_, rfl⟩
          simp [decodeArm, bind, Option.bind, ha, hkd, pure]
      | wide => exact absurd hkd (hn htr)

/-- `roundtrip`, keeping pointer views (the codec moves pointer words whole). -/
theorem roundtrip_wle {t a : Ty} {j : Nat} {p q : List Word} (ht : t.tier ≠ .boxed)
    (ha : (armsOf t)[j]? = some a) (hp : PayOK a p) (he : encodeArm t.tier (armsOf t) j p = some q) :
    ∃ p', decodeArm t.tier (armsOf t) q = some (j, p') ∧ WLe p p' := by
  have hm := getElem?_mem ha
  obtain ⟨⟨k, hk, hk1⟩, hn⟩ := arm_of_tier ht hm
  have hA := atom_of_mem t a hm
  obtain ⟨hl, hptr, hopt⟩ := hp
  cases htr : t.tier with
  | boxed => exact absurd htr ht
  | wide =>
      rw [htr] at he
      rw [hk] at hl; simp at hl
      match p, hl, he with
      | [], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[], ?_, trivial⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | [w], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[w], ?_, WLe_refl _⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | _ :: _ :: _, hl, _ => simp at hl; omega
  | niche =>
      rw [htr] at he
      simp only [encodeArm, bind, Option.bind, ha] at he
      cases hkd : armK a with
      | ptr =>
          obtain ⟨w, adr, rfl, hw⟩ := hptr hkd
          simp [hkd, hw] at he; subst he
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          refine ⟨[{ w with val := .loc adr 0 }], ?_, ⟨hw, fun _ _ _ => Nat.le_refl _⟩, trivial⟩
          simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | opt =>
          obtain ⟨w, rfl, hw⟩ := hopt hkd
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          rcases hw with hw | ⟨adr, hw⟩
          · simp [hkd, hw] at he; subst he
            refine ⟨[cst .null], ?_, ⟨hw, fun a g h => by rw [hw] at h; cases h⟩, trivial⟩
            simp [decodeArm, bind, Option.bind, ha, hkd, pure]
          · simp [hkd, hw] at he; subst he
            refine ⟨[{ w with val := .loc adr 0 }], ?_, ⟨hw, fun _ _ _ => Nat.le_refl _⟩, trivial⟩
            simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | nil =>
          have := atom_nil hA hkd
          rw [this] at hl; simp at hl
          have hl := hl.symm; rw [List.length_eq_zero_iff] at hl; subst hl
          simp [hkd] at he; subst he
          refine ⟨[], ?_, trivial⟩
          simp [decodeArm, bind, Option.bind, ha, hkd, pure]
      | wide => exact absurd hkd (hn htr)

/-- The heads the machine matches on survive in the skeleton. -/
theorem skel_eq_prod {rt a b : Ty} (h : skel rt = .prod a b) :
    ∃ ra rb, rt = .prod ra rb ∧ skel ra = a ∧ skel rb = b := by
  cases rt with
  | prod ra rb => simp only [skel, Ty.prod.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem skel_eq_iex {rt b : Ty} (h : skel rt = .iex b) : ∃ rb, rt = .iex rb ∧ skel rb = b := by
  cases rt with
  | iex rb => simp only [skel, Ty.iex.injEq] at h; exact ⟨rb, rfl, h⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem skel_eq_tex {rt : Ty} {κ : Kind} {b : Ty} (h : skel rt = .tex κ b) :
    ∃ rb, rt = .tex κ rb ∧ skel rb = b := by
  cases rt with
  | tex κ' rb => simp only [skel, Ty.tex.injEq] at h; obtain ⟨rfl, h⟩ := h; exact ⟨rb, rfl, h⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem skel_eq_fix {rt : Ty} {sg : Bool} {w : Wd} (h : skel rt = .fix sg w) : rt = .fix sg w := by
  cases rt with
  | fix => simpa [skel] using h
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem skel_eq_lanes {rt : Ty} {sg : Bool} {w : Wd} (h : skel rt = .lanes sg w) : rt = .lanes sg w := by
  cases rt with
  | lanes => simpa [skel] using h
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

/-! (T3d-1) The same through token erasure: `etok` makes nothing but `Unit`. -/

theorem eskel_eq_prod {rt a b : Ty} (h : etok (skel rt) = .prod a b) :
    ∃ ra rb, rt = .prod ra rb ∧ etok (skel ra) = a ∧ etok (skel rb) = b := by
  cases rt with
  | prod ra rb => simp only [skel, etok, Ty.prod.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

theorem eskel_eq_iex {rt b : Ty} (h : etok (skel rt) = .iex b) : ∃ rb, rt = .iex rb ∧ skel rb = b := by
  cases rt with
  | iex rb => simp only [skel, etok, Ty.iex.injEq] at h; exact ⟨rb, rfl, h⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

theorem eskel_eq_tex {rt : Ty} {κ : Kind} {b : Ty} (h : etok (skel rt) = .tex κ b) :
    ∃ rb, rt = .tex κ rb ∧ skel rb = b := by
  cases rt with
  | tex κ' rb => simp only [skel, etok, Ty.tex.injEq] at h; obtain ⟨rfl, h⟩ := h; exact ⟨rb, rfl, h⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

theorem eskel_eq_fix {rt : Ty} {sg : Bool} {w : Wd} (h : etok (skel rt) = .fix sg w) : rt = .fix sg w := by
  cases rt with
  | fix => simpa [skel, etok] using h
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

theorem eskel_eq_lanes {rt : Ty} {sg : Bool} {w : Wd} (h : etok (skel rt) = .lanes sg w) : rt = .lanes sg w := by
  cases rt with
  | lanes => simpa [skel, etok] using h
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

/-- Any integer type's skeleton, after any substitution, is `Int`. -/
theorem skel_intOf {t : Ty} {o : Option Idx} (h : intOf t = some o) (σs : List Ty) (c d : Nat) :
    skel (substTs σs c d t) = .int := by
  induction t with
  | intS => rfl
  | int => rfl
  | refine t ψ ih => simp only [intOf] at h; simp only [substTs, skel, ih h]; rfl
  | _ => simp [intOf] at h

/-- `ShapeC` depends on the runtime type only through its word count. -/
theorem ShapeC_wc {r r' : Ty} {ws : List Word} (h : wc r = wc r') (hs : ShapeC r ws) : ShapeC r' ws := by
  intro us hu
  have e : wc r = some (nWords us) := by rw [h]; simp [wc, hu]
  obtain ⟨us', hu', hn⟩ := wc_some e
  rw [hs us' hu', hn]

/-! ## §3 The frame invariant -/

theorem shape_fix (sg : Bool) (w : Wd) (x : Word) : ShapeC (.fix sg w) [x] := by
  intro us h; simp [accs] at h; subst h; rfl

theorem shape_lanes (sg : Bool) (w : Wd) (x : Word) : ShapeC (.lanes sg w) [x] := by
  intro us h; simp [accs] at h; subst h; rfl

/-! ### Transporting arm facts -/

theorem ArmLe.trans {a b c : Ty} (h1 : ArmLe a b) (h2 : ArmLe b c) : ArmLe a c := by
  refine ⟨?_, h1.2.trans h2.2⟩
  rcases h1.1 with e1 | ⟨e1, f1⟩ <;> rcases h2.1 with e2 | ⟨e2, f2⟩
  · exact Or.inl (e1.trans e2)
  · exact Or.inr ⟨e1.trans e2, f2⟩
  · exact Or.inr ⟨e1, e2.symm.trans f1⟩
  · rw [f1] at e2; simp at e2

theorem ArmsLe.trans {as bs cs : List Ty} (h1 : ArmsLe as bs) (h2 : ArmsLe bs cs) : ArmsLe as cs := by
  induction h1 generalizing cs with
  | nil => cases h2; exact .nil
  | cons hab _ ih => cases h2 with
    | cons hbc h2 => exact .cons (hab.trans hbc) (ih h2)

theorem ArmsLe.append {as bs cs ds : List Ty} (h1 : ArmsLe as bs) (h2 : ArmsLe cs ds) :
    ArmsLe (as ++ cs) (bs ++ ds) := by
  induction h1 with
  | nil => exact h2
  | cons hab _ ih => exact .cons hab ih

theorem ArmsLe.length {as bs : List Ty} (h : ArmsLe as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem forall2_map_left {R : Ty → Ty → Prop} {f : Ty → Ty} :
    ∀ (l : List Ty), (∀ a ∈ l, R (f a) a) → ArmsLeR R (l.map f) l
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall2_map_left l (fun x hx => h x (by simp [hx])))

theorem ArmLe.of_info {a b : Ty} (h : info Ty.top a = info Ty.top b) : ArmLe a b :=
  ArmLe.of_arms (by rw [h]) (by simp only [Ty.rawWords, Ty.width, h])

theorem armsOf_rf (t : Ty) : armsOf (rf t) = armsOf t := by cases t <;> rfl

theorem armsOf_skel : ∀ t : Ty, armsOf (skel t) = (armsOf t).map skel := by
  intro t; induction t <;> simp_all [skel, armsOf, armsOf_rf]

theorem sumHead_rf (t : Ty) : sumHead (rf t) = sumHead t := by cases t <;> rfl

theorem sumHead_skel : ∀ t : Ty, sumHead (skel t) = sumHead t := by
  intro t; induction t <;> simp_all [skel, sumHead, sumHead_rf]

theorem tier_skel (t : Ty) : (skel t).tier = t.tier := by simp only [Ty.tier, info_skel]

theorem arms_skel (t : Ty) : ArmsLe (armsOf t) (armsOf (skel t)) := by
  rw [armsOf_skel]; exact forall2_map _ (fun a _ => ArmLe.of_info (info_skel a Ty.top).symm)

theorem arms_skel' (t : Ty) : ArmsLe (armsOf (skel t)) (armsOf t) := by
  rw [armsOf_skel]; exact forall2_map_left _ (fun a _ => ArmLe.of_info (info_skel a Ty.top))

theorem ofArm_mono {t t' : Ty} {j : Nat} {p q : List Word} (hs : sumHead t = sumHead t')
    (ht : t.tier = t'.tier) (ha : ArmsLe (armsOf t) (armsOf t')) (h : ofArm t j p = some q) :
    ofArm t' j p = some q := by
  unfold ofArm at h ⊢
  rw [← hs, ← ht]
  split at h
  · rename_i h1; rw [if_pos h1]; exact encodeArm_mono ha h
  · rename_i h1; rw [if_neg h1]; exact h

/-! ### Runtime validity -/

theorem ShapeC_vals {t : Ty} {ws ws' : List Word} (e : VEq ws ws') (h : ShapeC t ws) : ShapeC t ws' := by
  intro us hu; rw [← h us hu]; simpa using (congrArg List.length e).symm

theorem SumV_vals {Va Vb Va' Vb' : List Word → Prop} {a b : Ty} {ws ws' : List Word} (e : VEq ws ws')
    (hva : ∀ q q', VEq q q' → Va q → Va' q') (hvb : ∀ q q', VEq q q' → Vb q → Vb' q')
    (h : SumV Va Vb a b ws) : SumV Va' Vb' a b ws' := by
  rcases h with h | ⟨j, p, arm, hd, ha, hp, ⟨q, hq, eq⟩, h1, h2⟩
  · exact Or.inl h
  obtain ⟨p', hd', ep⟩ := decodeArm_vals e hd
  obtain ⟨q', hq', eq'⟩ := encodeArm_vals ep hq
  refine Or.inr ⟨j, p', arm, hd', ha, PayOK_vals ep hp, ⟨q', hq', ?_⟩, fun hj => ?_, fun hj => ?_⟩
  · exact (eq'.symm.trans eq).trans e
  · obtain ⟨r, hr, hs, hw, hv⟩ := h1 hj
    obtain ⟨r', hr', er⟩ := ofArm_vals ep hr
    exact ⟨r', hr', ShapeC_vals er hs, hw, hva _ _ er hv⟩
  · obtain ⟨r, hr, hs, hw, hv⟩ := h2 hj
    obtain ⟨r', hr', er⟩ := ofArm_vals ep hr
    exact ⟨r', hr', ShapeC_vals er hs, hw, hvb _ _ er hv⟩

/-- **`Valid` reads only values.** -/
theorem Valid_vals : ∀ (t : Ty) (ws ws' : List Word), VEq ws ws' → Valid t ws → Valid t ws' := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ws ws' e hv n hn
      obtain ⟨h1, h2⟩ := hv n hn
      exact ⟨iha _ _ (by simp only [VEq, List.map_take, e]) h1,
        ihb _ _ (by simp only [VEq, List.map_drop, e]) h2⟩
  | sum a b iha ihb =>
      intro ws ws' e hv
      exact SumV_vals e (fun q q' eq hq => iha q q' eq hq) (fun q q' eq hq => ihb q q' eq hq) hv
  | refine t _ ih => intro ws ws' e hv; exact ih ws ws' e hv
  | iall t ih => intro ws ws' e hv; exact ih ws ws' e hv
  | iex t ih => intro ws ws' e hv; exact ih ws ws' e hv
  | mu t ih => intro ws ws' e hv; exact ih ws ws' e hv
  | tex κ t ih => intro ws ws' e hv; exact ih ws ws' e hv
  | ptr => intro ws ws' e hv; simp only [Valid] at hv ⊢; rw [← e]; exact hv
  | ptrOpt => intro ws ws' e hv; simp only [Valid] at hv ⊢; rw [← e]; exact hv
  | loc => intro ws ws' e hv; simp only [Valid] at hv ⊢; rw [← e]; exact hv
  | void => intro ws ws' e hv; exact hv
  | _ => intro ws ws' e hv; trivial

/-- Transport of the sum case along arms that only grow (`Ptr ≤ Ptr?`). -/
theorem SumV_mono {Va Vb Va' Vb' : List Word → Prop} {a b a' b' : Ty} {ws : List Word}
    (ht : (Ty.sum a b).tier = (Ty.sum a' b').tier)
    (hA : ArmsLe (armsOf a) (armsOf a')) (hB : ArmsLe (armsOf b) (armsOf b'))
    (hsa : sumHead a = sumHead a') (hsb : sumHead b = sumHead b')
    (hta : a.tier = a'.tier) (htb : b.tier = b'.tier) (hwa : wc a = wc a') (hwb : wc b = wc b')
    (hva : ∀ q, Va q → Va' q) (hvb : ∀ q, Vb q → Vb' q)
    (h : SumV Va Vb a b ws) : SumV Va' Vb' a' b' ws := by
  have hAB : ArmsLe (armsOf (.sum a b)) (armsOf (.sum a' b')) := hA.append hB
  rcases h with h | ⟨j, p, arm, hd, ha, hp, ⟨q, hq, eq⟩, h1, h2⟩
  · exact Or.inl (ht ▸ h)
  obtain ⟨arm', ha', hle⟩ := get_mono hAB ha
  refine Or.inr ⟨j, p, arm', ht ▸ decodeArm_mono hAB hd, ha', PayOK_mono hle hp,
    ⟨q, ht ▸ encodeArm_mono hAB hq, eq⟩, fun hj => ?_, fun hj => ?_⟩
  · rw [← hA.length] at hj
    obtain ⟨r, hr, hs, hw, hv⟩ := h1 hj
    exact ⟨r, ofArm_mono hsa hta hA hr, ShapeC_wc hwa hs, hwa ▸ hw, hva _ hv⟩
  · rw [← hA.length] at hj ⊢
    obtain ⟨r, hr, hs, hw, hv⟩ := h2 hj
    exact ⟨r, ofArm_mono hsb htb hB hr, ShapeC_wc hwb hs, hwb ▸ hw, hvb _ hv⟩

theorem Valid_rf (t : Ty) (ws : List Word) : Valid (rf t) ws ↔ Valid t ws := by
  cases t <;> simp [rf, Valid]

/-- **`Valid` sees only the skeleton.** -/
theorem Valid_skel : ∀ (t : Ty) (ws : List Word), Valid (skel t) ws ↔ Valid t ws := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro ws
      simp only [skel, Valid, wc_skel, iha, ihb]
  | sum a b iha ihb =>
      intro ws
      have ht : (Ty.sum (skel a) (skel b)).tier = (Ty.sum a b).tier := tier_skel (.sum a b)
      simp only [skel, Valid]
      constructor
      · exact SumV_mono ht (arms_skel' a) (arms_skel' b) (sumHead_skel a) (sumHead_skel b)
          (tier_skel a) (tier_skel b) (wc_skel a) (wc_skel b) (fun q h => (iha q).1 h) (fun q h => (ihb q).1 h)
      · exact SumV_mono ht.symm (arms_skel a) (arms_skel b) (sumHead_skel a).symm (sumHead_skel b).symm
          (tier_skel a).symm (tier_skel b).symm (wc_skel a).symm (wc_skel b).symm
          (fun q h => (iha q).2 h) (fun q h => (ihb q).2 h)
  | refine t ψ ih => intro ws; simp only [skel, Valid_rf, Valid, ih]
  | iall t ih => intro ws; simp only [skel, Valid, ih]
  | iex t ih => intro ws; simp only [skel, Valid, ih]
  | mu t ih => intro ws; simp only [skel, Valid, ih]
  | tex κ t ih => intro ws; simp only [skel, Valid, ih]
  | _ => intro ws; simp [skel, Valid]

theorem Valid_of_skel {t u : Ty} {ws : List Word} (h : skel t = skel u) (hv : Valid t ws) : Valid u ws := by
  rw [← Valid_skel] at hv ⊢; rw [← h]; exact hv

theorem arms_of_skel {t u : Ty} (h : skel t = skel u) : ArmsLe (armsOf t) (armsOf u) :=
  (arms_skel t).trans (h ▸ arms_skel' u)

theorem sumHead_of_skel {t u : Ty} (h : skel t = skel u) : sumHead t = sumHead u := by
  rw [← sumHead_skel t, h, sumHead_skel]

/-! ### Signatures (24e): `sig` keeps everything a layout reads -/

theorem info_er : ∀ (t : Ty) (ρ : Ctx), (∀ k, ρ k = none) → info ρ (er t) = info ρ t := by
  intro t
  induction t with
  | prod a b iha ihb => intro ρ hρ; simp only [er, info, iha ρ hρ, ihb ρ hρ]
  | sum a b iha ihb => intro ρ hρ; simp only [er, info, iha ρ hρ, ihb ρ hρ]
  | mu t ih =>
      intro ρ hρ; simp only [er, info]; exact ih _ (fun k => by cases k <;> simp [Ctx.cons, hρ])
  | tex κ t ih =>
      intro ρ hρ; simp only [er, info]; exact ih _ (fun k => by cases k <;> simp [Ctx.cons, hρ])
  | iall t ih => intro ρ hρ; simp only [er, info, ih ρ.shiftI (fun k => by simp [Ctx.shiftI, hρ])]
  | iex t ih => intro ρ hρ; simp only [er, info, ih ρ.shiftI (fun k => by simp [Ctx.shiftI, hρ])]
  | refine t ψ ih => intro ρ hρ; simp only [er, info, ih ρ hρ]
  | tvar k => intro ρ hρ; simp only [er, info, hρ]
  | _ => intro ρ _; rfl

theorem tier_er (t : Ty) : (er t).tier = t.tier := by
  simp only [Ty.tier, info_er t Ty.top (fun _ => rfl)]

theorem wc_er : ∀ t : Ty, wc (er t) = wc t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [er, wc_prod, iha, ihb]
  | sum a b _ _ =>
      have e := info_er (.sum a b) Ty.top (fun _ => rfl)
      simp only [er] at e
      simp only [er, wc, accs, Ty.tier, e]
      by_cases hT : (info Ty.top (a.sum b)).arms.tier = Tier.wide <;> simp only [hT] <;> rfl
  | refine t ψ ih => simp only [er]; simp only [wc, accs] at ih ⊢; exact ih
  | mu t ih => simp only [er, wc, accs] at ih ⊢; exact ih
  | iall t ih => simp only [er, wc, accs] at ih ⊢; exact ih
  | iex t ih => simp only [er, wc_iex, ih]
  | tex κ t ih => simp only [er, wc_tex, ih]
  | _ => rfl

theorem armsOf_er : ∀ t : Ty, armsOf (er t) = (armsOf t).map er := by
  intro t; induction t <;> simp_all [er, armsOf]

theorem sumHead_er : ∀ t : Ty, sumHead (er t) = sumHead t := by
  intro t; induction t <;> simp_all [er, sumHead]

theorem arms_er (t : Ty) : ArmsLe (armsOf t) (armsOf (er t)) := by
  rw [armsOf_er]; exact forall2_map _ (fun a _ => ArmLe.of_info (info_er a Ty.top (fun _ => rfl)).symm)

theorem arms_er' (t : Ty) : ArmsLe (armsOf (er t)) (armsOf t) := by
  rw [armsOf_er]; exact forall2_map_left _ (fun a _ => ArmLe.of_info (info_er a Ty.top (fun _ => rfl)))

theorem Valid_er : ∀ (t : Ty) (ws : List Word), Valid (er t) ws ↔ Valid t ws := by
  intro t
  induction t with
  | prod a b iha ihb => intro ws; simp only [er, Valid, wc_er, iha, ihb]
  | sum a b iha ihb =>
      intro ws
      have ht : (Ty.sum (er a) (er b)).tier = (Ty.sum a b).tier := tier_er (.sum a b)
      simp only [er, Valid]
      constructor
      · exact SumV_mono ht (arms_er' a) (arms_er' b) (sumHead_er a) (sumHead_er b)
          (tier_er a) (tier_er b) (wc_er a) (wc_er b) (fun q h => (iha q).1 h) (fun q h => (ihb q).1 h)
      · exact SumV_mono ht.symm (arms_er a) (arms_er b) (sumHead_er a).symm (sumHead_er b).symm
          (tier_er a).symm (tier_er b).symm (wc_er a).symm (wc_er b).symm
          (fun q h => (iha q).2 h) (fun q h => (ihb q).2 h)
  | refine t ψ ih => intro ws; simp only [er, Valid, ih]
  | iall t ih => intro ws; simp only [er, Valid, ih]
  | iex t ih => intro ws; simp only [er, Valid, ih]
  | mu t ih => intro ws; simp only [er, Valid, ih]
  | tex κ t ih => intro ws; simp only [er, Valid, ih]
  | _ => intro ws; simp [er, Valid]

theorem sig_er (t : Ty) : sig (er t) = sig t := by simp only [sig, skel_er, er_idem]

theorem lnorm_er : ∀ t : Ty, lnorm (er t) = lnorm t := by
  intro t; induction t <;> simp_all [er, lnorm, sig_er]

theorem shp_er : ∀ t : Ty, shp (er t) = shp t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [er, shp, iha, ihb]
  | sum a b _ _ =>
      have e := wc_er (.sum a b); have el := lnorm_er (.sum a b)
      simp only [er] at e el ⊢; simp only [shp, e, el]
  | code a b _ _ => simp only [er, shp, sig_er]
  | iex t ih => have e := wc_er (.iex t); simp only [er] at e ⊢; simp only [shp, e, ih]
  | tex κ t ih => have e := wc_er (.tex κ t); simp only [er] at e ⊢; simp only [shp, e, ih]
  | refine t ψ ih => simp only [er, shp, ih]
  | array i t _ => have e := wc_er (.array i t); simp only [er] at e ⊢; simp only [shp, e]
  | ptr μ t _ => rfl
  | ptrOpt μ t _ => rfl
  | loc μ t _ => rfl
  | mu t ih => simp only [er, shp, ih]
  | iall t ih => simp only [er, shp, ih]
  | _ => rfl

theorem wc_sig (t : Ty) : wc (sig t) = wc t := by simp only [sig, wc_er, wc_skel]
theorem shp_sig (t : Ty) : shp (sig t) = shp t := by simp only [sig, shp_er, shp_skel]
theorem Valid_sig (t : Ty) (ws : List Word) : Valid (sig t) ws ↔ Valid t ws := by
  simp only [sig, Valid_er, Valid_skel]

theorem wc_of_sig {t u : Ty} (h : sig t = sig u) : wc t = wc u := by rw [← wc_sig t, h, wc_sig]
theorem shp_of_sig {t u : Ty} (h : sig t = sig u) : shp t = shp u := by rw [← shp_sig t, h, shp_sig]
theorem Valid_of_sig {t u : Ty} {ws : List Word} (h : sig t = sig u) (hv : Valid t ws) : Valid u ws := by
  rw [← Valid_sig] at hv ⊢; rw [← h]; exact hv

/-! ### (T3d-1) Token erasure: nothing a layout reads sees a token -/

theorem info_etok : ∀ (t : Ty) (ρ : Ctx), info ρ (etok t) = info ρ t := by
  intro t
  induction t with
  | prod a b iha ihb => intro ρ; simp only [etok, info, iha ρ, ihb ρ]
  | sum a b iha ihb => intro ρ; simp only [etok, info, iha ρ, ihb ρ]
  | refine t ψ ih => intro ρ; simp only [etok, info, ih ρ]
  | _ => intro ρ; rfl

theorem tier_etok (t : Ty) : (etok t).tier = t.tier := by
  simp only [Ty.tier, info_etok t Ty.top]

theorem accs_etok : ∀ t : Ty, accs (etok t) = accs t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [etok, accs, iha, ihb]
  | sum a b _ _ =>
      have e := info_etok (.sum a b) Ty.top
      simp only [etok] at e
      simp only [etok, accs, Ty.tier, e]
      by_cases hT : (info Ty.top (a.sum b)).arms.tier = Tier.wide <;> simp only [hT] <;> rfl
  | refine t ψ ih => simp only [etok, accs, ih]
  | _ => rfl

theorem wc_etok (t : Ty) : wc (etok t) = wc t := by simp only [wc, accs_etok]

theorem sumHead_etok : ∀ t : Ty, sumHead (etok t) = sumHead t := by
  intro t; induction t <;> simp_all [etok, sumHead]

theorem ArmsLeR_refl {R : Ty → Ty → Prop} (hR : ∀ a, R a a) : ∀ l : List Ty, ArmsLeR R l l
  | [] => .nil
  | a :: l => .cons (hR a) (ArmsLeR_refl hR l)

theorem ArmsLeR_append {R : Ty → Ty → Prop} {as bs cs ds : List Ty} (h1 : ArmsLeR R as bs)
    (h2 : ArmsLeR R cs ds) : ArmsLeR R (as ++ cs) (bs ++ ds) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

/-- `etok` stops at `μ`, `∃`, `∀` and type packages, whose arms it leaves alone;
elsewhere every arm is erased to one with the same `info`. -/
theorem arms_etok : ∀ t : Ty, ArmsLe (armsOf t) (armsOf (etok t)) := by
  intro t
  induction t with
  | sum a b iha ihb => exact ArmsLeR_append iha ihb
  | refine t ψ ih => exact ih
  | mu t _ => exact ArmsLeR_refl ArmLe.refl _
  | tex κ t _ => exact ArmsLeR_refl ArmLe.refl _
  | iall t _ => exact ArmsLeR_refl ArmLe.refl _
  | iex t _ => exact ArmsLeR_refl ArmLe.refl _
  | void => exact .nil
  | _ => exact .cons (ArmLe.of_info (info_etok _ Ty.top).symm) .nil

theorem arms_etok' : ∀ t : Ty, ArmsLe (armsOf (etok t)) (armsOf t) := by
  intro t
  induction t with
  | sum a b iha ihb => exact ArmsLeR_append iha ihb
  | refine t ψ ih => exact ih
  | mu t _ => exact ArmsLeR_refl ArmLe.refl _
  | tex κ t _ => exact ArmsLeR_refl ArmLe.refl _
  | iall t _ => exact ArmsLeR_refl ArmLe.refl _
  | iex t _ => exact ArmsLeR_refl ArmLe.refl _
  | void => exact .nil
  | _ => exact .cons (ArmLe.of_info (info_etok _ Ty.top)) .nil

theorem Valid_etok : ∀ (t : Ty) (ws : List Word), Valid (etok t) ws ↔ Valid t ws := by
  intro t
  induction t with
  | prod a b iha ihb => intro ws; simp only [etok, Valid, wc_etok, iha, ihb]
  | sum a b iha ihb =>
      intro ws
      have ht : (Ty.sum (etok a) (etok b)).tier = (Ty.sum a b).tier := tier_etok (.sum a b)
      simp only [etok, Valid]
      constructor
      · exact SumV_mono ht (arms_etok' a) (arms_etok' b) (sumHead_etok a) (sumHead_etok b)
          (tier_etok a) (tier_etok b) (wc_etok a) (wc_etok b) (fun q h => (iha q).1 h) (fun q h => (ihb q).1 h)
      · exact SumV_mono ht.symm (arms_etok a) (arms_etok b) (sumHead_etok a).symm (sumHead_etok b).symm
          (tier_etok a).symm (tier_etok b).symm (wc_etok a).symm (wc_etok b).symm
          (fun q h => (iha q).2 h) (fun q h => (ihb q).2 h)
  | refine t ψ ih => intro ws; simp only [etok, Valid, ih]
  | _ => intro ws; simp [etok, Valid]

theorem lnorm_etok : ∀ t : Ty, lnorm (etok t) = lnorm t := by
  intro t; induction t <;> simp_all [etok, lnorm]

theorem shp_etok : ∀ t : Ty, shp (etok t) = shp t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [etok, shp, iha, ihb]
  | sum a b _ _ =>
      have e := wc_etok (.sum a b); have el := lnorm_etok (.sum a b)
      simp only [etok] at e el ⊢; simp only [shp, e, el]
  | code a b _ _ => simp only [etok, shp]
  | refine t ψ ih => simp only [etok, shp, ih]
  | array i t _ => have e := wc_etok (.array i t); simp only [etok] at e ⊢; simp only [shp, e]
  | ptr μ t _ => have e := wc_etok (.ptr μ t); simp only [etok] at e ⊢; simp only [shp, e]
  | ptrOpt μ t _ => have e := wc_etok (.ptrOpt μ t); simp only [etok] at e ⊢; simp only [shp, e]
  | loc μ t _ => have e := wc_etok (.loc μ t); simp only [etok] at e ⊢; simp only [shp, e]
  | _ => rfl

/-- `er` erases what `etok` erases. -/
theorem er_etok : ∀ t : Ty, er (etok t) = er t := by
  intro t; induction t <;> simp_all [etok, er]

theorem etok_idem : ∀ t : Ty, etok (etok t) = etok t := by
  intro t; induction t <;> simp_all [etok]

theorem etok_rf (t : Ty) : etok (rf t) = rf (etok t) := by cases t <;> rfl

theorem etok_skel : ∀ t : Ty, etok (skel t) = skel (etok t) := by
  intro t; induction t <;> simp_all [etok, skel, etok_rf]

/-- `sig` through a skeleton equality modulo tokens. -/
theorem sig_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : sig t = sig u := by
  show er (skel t) = er (skel u)
  rw [← er_etok (skel t), h, er_etok]

theorem shp_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : shp t = shp u := by
  rw [← shp_skel t, ← shp_etok (skel t), h, shp_etok, shp_skel]

theorem wc_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : wc t = wc u := by
  rw [← wc_skel t, ← wc_etok (skel t), h, wc_etok, wc_skel]

theorem Valid_of_eskel {t u : Ty} {ws : List Word} (h : etok (skel t) = etok (skel u)) (hv : Valid t ws) :
    Valid u ws := by
  rw [← Valid_skel, ← Valid_etok] at hv ⊢; rw [← h]; exact hv

theorem sumHead_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : sumHead t = sumHead u := by
  rw [← sumHead_skel t, ← sumHead_etok (skel t), h, sumHead_etok, sumHead_skel]

theorem arms_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : ArmsLe (armsOf t) (armsOf u) :=
  ((arms_skel t).trans (arms_etok _)).trans (h ▸ (arms_etok' _).trans (arms_skel' u))

theorem eskel_of_skel {t u : Ty} (h : skel t = skel u) : etok (skel t) = etok (skel u) := by rw [h]

/-! ### T3c-4a: layout agreement of `close σs` and `cl ρ W`

TermRun lays values out at runtime types, renditions of `close σs t`; Σ holds
closed static types `cl ρ η.wit 0 0 t`.  The two differ only at type variables
(`unpackT` runs at `Unit` for the erased witness), and word counts, shapes and
`Valid` read only `sig`, which erases pointees.  So they agree whenever every
variable occurring outside a reference agrees in `sig`. -/

theorem skelM_clM (ρ : Nat → Nat) (d : Nat) (μ : Mode) : skelM (clM ρ d μ) = skelM μ := by
  cases μ <;> rfl

theorem sig_substTs_tvar (σs : List Ty) (c d k : Nat) :
    sig (substTs σs c d (.tvar (c + k))) = sig (close σs (.tvar k)) := by
  have h1 : ¬ c + k < c := by omega
  have h2 : c + k - c = k := by omega
  simp only [close, substTs, h1, h2, if_false, Nat.not_lt_zero, Nat.sub_zero]
  cases σs[k]? with
  | none => rfl
  | some σ => simp only [sig_shiftIN, sig_shiftTN]

theorem sig_close_cl (σs : List Ty) (ρ : Nat → Nat) (W : Nat → Ty) :
    ∀ (t : Ty) (c d : Nat), (∀ k, t.guardT (c + k) = false → sig (close σs (.tvar k)) = sig (W k)) →
      sig (substTs σs c d t) = sig (cl ρ W c d t) := by
  intro t
  induction t with
  | tvar j =>
      intro c d H
      by_cases hj : j < c
      · simp [substTs, cl, hj, sig, skel, er]
      · obtain ⟨k, rfl⟩ : ∃ k, j = c + k := ⟨j - c, by omega⟩
        rw [sig_substTs_tvar, H k (by simp [Ty.guardT])]
        have e : c + k - c = k := by omega
        simp only [cl, hj, e, if_false]
  | prod a b iha ihb =>
      intro c d H
      have e1 := iha c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      have e2 := ihb c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      simp only [sig] at e1 e2
      simp only [substTs, cl, sig, skel, er, e1, e2]
  | sum a b iha ihb =>
      intro c d H
      have e1 := iha c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      have e2 := ihb c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      simp only [sig] at e1 e2
      simp only [substTs, cl, sig, skel, er, e1, e2]
  | code a b iha ihb =>
      intro c d H
      have e1 := iha c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      have e2 := ihb c d (fun k hk => H k (by simp [Ty.guardT, hk]))
      simp only [sig] at e1 e2
      simp only [substTs, cl, sig, skel, er, e1, e2]
  | array i t ih =>
      intro c d H
      have e1 := ih c d (fun k hk => H k (by simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er, e1]
  | ptr μ t _ => intro c d _; simp only [substTs, cl, sig, skel, er, skelM_clM]
  | ptrOpt μ t _ => intro c d _; simp only [substTs, cl, sig, skel, er, skelM_clM]
  | loc μ t _ => intro c d _; simp only [substTs, cl, sig, skel, er, skelM_clM]
  | mu t ih =>
      intro c d H
      have e1 := ih (c + 1) d (fun k hk => H k (by
        have e : c + 1 + k = c + k + 1 := by omega
        rw [e] at hk; simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er, e1]
  | tex κ t ih =>
      intro c d H
      have e1 := ih (c + 1) d (fun k hk => H k (by
        have e : c + 1 + k = c + k + 1 := by omega
        rw [e] at hk; simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er, e1]
  | iall t ih =>
      intro c d H
      have e1 := ih c (d + 1) (fun k hk => H k (by simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er, e1]
  | iex t ih =>
      intro c d H
      have e1 := ih c (d + 1) (fun k hk => H k (by simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er, e1]
  | refine t ψ ih =>
      intro c d H
      have e1 := ih c d (fun k hk => H k (by simpa [Ty.guardT] using hk))
      simp only [sig] at e1
      simp only [substTs, cl, sig, skel, er_rf, e1]
  | _ => intro c d _; rfl

/-- A well-formed type's variables are below `nt`, so every variable from
`nt` on is guarded (vacuously). -/
theorem guardT_of_wf : ∀ (t : Ty) (nt ni k : Nat), t.wf nt ni = true → nt ≤ k → t.guardT k = true := by
  intro t
  induction t with
  | tvar j =>
      intro nt ni k h hk
      simp only [Ty.wf, decide_eq_true_eq] at h
      simp only [Ty.guardT, bne_iff_ne, ne_eq]; omega
  | prod a b iha ihb =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, iha nt ni k h.1 hk, ihb nt ni k h.2 hk, Bool.and_self]
  | sum a b iha ihb =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, iha nt ni k h.1 hk, ihb nt ni k h.2 hk, Bool.and_self]
  | code a b iha ihb =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, iha nt ni k h.1 hk, ihb nt ni k h.2 hk, Bool.and_self]
  | array i t ih =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, ih nt ni k h.2 hk]
  | mu t ih =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, ih (nt + 1) ni (k + 1) h.2 (by omega)]
  | tex κ t ih =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, ih (nt + 1) ni (k + 1) h.2 (by omega)]
  | iall t ih => intro nt ni k h hk; simp only [Ty.wf] at h; simp only [Ty.guardT, ih nt (ni + 1) k h hk]
  | iex t ih => intro nt ni k h hk; simp only [Ty.wf] at h; simp only [Ty.guardT, ih nt (ni + 1) k h hk]
  | refine t ψ ih =>
      intro nt ni k h hk; simp only [Ty.wf, Bool.and_eq_true] at h
      simp only [Ty.guardT, ih nt ni k h.2 hk]
  | _ => intro nt ni k _ _; rfl

/-! ### Zero agreement (T3c-5b, option (1) for `newBuf`)

`newBuf` zeroes a buffer when the *runtime* rendition `close σs τ` of its
element type is `Zeroable`, but the cells must be values of the *witness*
rendition `cl ρ W 0 0 τ`.  `WitL`'s `sig` agreement erases singleton
indices, refinements and a `Loc`'s length, so the frame also keeps `ZRel`:
the two renditions of each type argument agree on everything a zero relies
on.  `zrel_close_cl` lifts it from the arguments to any type.  (`EnvSh` and
its lemmas moved here from KindSound.) -/

/-- `env'` is `env` with one entry inserted at `c`. -/
def EnvSh (c : Nat) (env' env : IEnv) : Prop :=
  ∀ k, env'[if k ≥ c then k + 1 else k]?.join = env[k]?.join

theorem EnvSh.cons {c : Nat} {env' env : IEnv} (h : EnvSh c env' env) (v : Option Nat) :
    EnvSh (c + 1) (v :: env') (v :: env) := by
  intro k
  cases k with
  | zero => simp
  | succ k =>
      have e := h k
      by_cases hk : k ≥ c
      · rw [if_pos hk] at e; rw [if_pos (by omega : k + 1 ≥ c + 1)]; simpa using e
      · rw [if_neg hk] at e; rw [if_neg (by omega : ¬ (k + 1 ≥ c + 1))]; simpa using e

theorem EnvSh.nil (c : Nat) : EnvSh c [] [] := by intro k; simp

theorem EnvSh.drop (env : IEnv) : EnvSh 0 env (env.drop 1) := by
  intro k; simp

theorem evalIn_shift {c : Nat} {env' env : IEnv} (h : EnvSh c env' env) :
    ∀ i : Idx, (i.shift c).evalIn env' = i.evalIn env
  | .lit _ => rfl
  | .var k => by
      have := h k
      by_cases hk : k ≥ c
      · simp only [Idx.shift, hk, if_true, Idx.evalIn] at this ⊢; exact this
      · simp only [Idx.shift, hk, if_false, Idx.evalIn] at this ⊢; exact this
  | .add i j => by simp only [Idx.shift, Idx.evalIn, evalIn_shift h i, evalIn_shift h j]
  | .sub i j => by simp only [Idx.shift, Idx.evalIn, evalIn_shift h i, evalIn_shift h j]
  | .smul n i => by simp only [Idx.shift, Idx.evalIn, evalIn_shift h i]

theorem zeroHolds_shift {c : Nat} {env' env : IEnv} (h : EnvSh c env' env) :
    ∀ ψ : Pred, (ψ.shift c).zeroHolds env' = ψ.zeroHolds env
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.zeroHolds, evalIn_shift h]
  | .eq i j => by simp only [Pred.shift, Pred.zeroHolds, evalIn_shift h]
  | .and p q => by simp only [Pred.shift, Pred.zeroHolds, zeroHolds_shift h p, zeroHolds_shift h q]
  | .ini i => by simp only [Pred.shift, Pred.zeroHolds, evalIn_shift h]

/-! ## Zero agreement -/

/-- `i` is at least as known as `j` under `env`, and agrees where known. -/
def IdxLe (env : IEnv) (i j : Idx) : Prop := ∀ v, i.evalIn env = some v → j.evalIn env = some v

/-- What a null `Loc` needs of its pointee: a zero-length array on the left is
one on the right. -/
def LocZ (env : IEnv) : Ty → Ty → Prop
  | .array i _, .array j _ => IdxLe env i j
  | .array _ _, _ => False
  | _, _ => True

/-- **Zero agreement**: `R` (the runtime rendition) and `T` (the witness
rendition) have the same constructors down to references, and everything
the zero of `R` relies on (singleton indices, a null `Loc`'s length,
refinements) holds of `T` too. -/
def ZRel (env : IEnv) : Ty → Ty → Prop
  | .unit, .unit => True
  | .void, .void => True
  | .int, .int => True
  | .tid, .tid => True
  | .intS i, .intS j => IdxLe env i j
  | .fix _ _, .fix _ _ => True
  | .lanes _ _, .lanes _ _ => True
  | .prod a b, .prod a' b' => ZRel env a a' ∧ ZRel env b b'
  | .sum a b, .sum a' b' => ZRel env a a' ∧ ZRel env b b'
  | .code _ _, .code _ _ => True
  | .array i t, .array j u => IdxLe env i j ∧ ZRel env t u
  | .ptr _ _, .ptr _ _ => True
  | .ptrOpt _ _, .ptrOpt _ _ => True
  | .loc _ t, .loc _ u => LocZ env t u
  | .share _, .share _ => True
  | .cap _ _, .cap _ _ => True
  | .word _ _, .word _ _ => True
  | .tok _ _, .tok _ _ => True
  | .word2 _ _, .word2 _ _ => True
  | .tok2 _ _ _ _, .tok2 _ _ _ _ => True
  | .epair _ _, .epair _ _ => True
  | .tokE _ _ _, .tokE _ _ _ => True
  | .tvar _, .tvar _ => True
  | .mu t, .mu u => ZRel env t u
  | .tex _ t, .tex _ u => ZRel env t u
  | .iall t, .iall u => ZRel (none :: env) t u
  | .iex t, .iex u => ZRel (some 0 :: env) t u
  | .refine t ψ, .refine u φ => ZRel env t u ∧ (ψ.zeroHolds env = true → φ.zeroHolds env = true)
  | _, _ => False

theorem ZRel_loc {env : IEnv} : ∀ {R T : Ty}, ZRel env R T → LocZ env R T := by
  intro R T h
  cases R <;> cases T <;> simp only [ZRel, LocZ] at h ⊢ <;> exact h.1

theorem IdxLe_shift {c : Nat} {env' env : IEnv} (h : EnvSh c env' env) {i j : Idx}
    (hij : IdxLe env i j) : IdxLe env' (i.shift c) (j.shift c) := by
  intro v hv; rw [evalIn_shift h] at hv ⊢; exact hij v hv

theorem LocZ_shiftT {env : IEnv} (c : Nat) : ∀ {R T : Ty}, LocZ env R T → LocZ env (R.shiftT c) T := by
  intro R T h
  cases R <;> simp only [Ty.shiftT] <;> (try split) <;> cases T <;> simp_all [LocZ]

theorem ZRel_shiftT : ∀ (R : Ty) {env : IEnv} {T : Ty} (c : Nat), ZRel env R T → ZRel env (R.shiftT c) T := by
  intro R
  induction R with
  | tvar k => intro env T c h; cases T <;> simp only [ZRel] at h; simp only [Ty.shiftT]; split <;> simp [ZRel]
  | prod a b iha ihb => intro env T c h; cases T <;> simp only [ZRel] at h; exact ⟨iha c h.1, ihb c h.2⟩
  | sum a b iha ihb => intro env T c h; cases T <;> simp only [ZRel] at h; exact ⟨iha c h.1, ihb c h.2⟩
  | array i t ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ⟨h.1, ih c h.2⟩
  | loc μ t _ => intro env T c h; cases T <;> simp only [ZRel] at h; exact LocZ_shiftT c h
  | mu t ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ih (c + 1) h
  | tex κ t ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ih (c + 1) h
  | iall t ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ih c h
  | iex t ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ih c h
  | refine t ψ ih => intro env T c h; cases T <;> simp only [ZRel] at h; exact ⟨ih c h.1, h.2⟩
  | _ => intro env T c h; cases T <;> simp only [ZRel] at h <;> trivial

theorem ZRel_shiftTN (c : Nat) : ∀ (n : Nat) {env : IEnv} {R T : Ty}, ZRel env R T → ZRel env (shiftTN n R) T
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => ZRel_shiftT _ 0 (ZRel_shiftTN c n h)

theorem LocZ_shiftTN : ∀ (n : Nat) {env : IEnv} {R T : Ty}, LocZ env R T → LocZ env (shiftTN n R) T
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => LocZ_shiftT 0 (LocZ_shiftTN n h)

theorem LocZ_shiftI {c : Nat} {env' env : IEnv} (hE : EnvSh c env' env) :
    ∀ {R T : Ty}, LocZ env R T → LocZ env' (R.shiftI c) (T.shiftI c) := by
  intro R T h
  cases R <;> cases T <;> simp only [Ty.shiftI, LocZ] at h ⊢ <;> first | trivial | exact IdxLe_shift hE h

theorem ZRel_shiftI : ∀ (R : Ty) {env' env : IEnv} {T : Ty} {c : Nat}, EnvSh c env' env →
    ZRel env R T → ZRel env' (R.shiftI c) (T.shiftI c) := by
  intro R
  induction R with
  | intS i => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact IdxLe_shift hE h
  | prod a b iha ihb => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ⟨iha hE h.1, ihb hE h.2⟩
  | sum a b iha ihb => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ⟨iha hE h.1, ihb hE h.2⟩
  | array i t ih => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ⟨IdxLe_shift hE h.1, ih hE h.2⟩
  | loc μ t _ => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact LocZ_shiftI hE h
  | mu t ih => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ih hE h
  | tex κ t ih => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ih hE h
  | iall t ih => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ih (hE.cons none) h
  | iex t ih => intro env' env T c hE h; cases T <;> simp only [ZRel] at h; exact ih (hE.cons (some 0)) h
  | refine t ψ ih =>
      intro env' env T c hE h; cases T <;> simp only [ZRel] at h
      refine ⟨ih hE h.1, fun hz => ?_⟩
      rw [zeroHolds_shift hE] at hz ⊢; exact h.2 hz
  | _ => intro env' env T c hE h; cases T <;> simp only [ZRel] at h <;> trivial

/-! ### Closed types have no free index variable -/

theorem clI_shift_id {ρ : Nat → Nat} {f c : Nat} (hf : f ≤ c) : ∀ i : Idx, (clI ρ f i).shift c = clI ρ f i
  | .lit _ => rfl
  | .var k => by
      by_cases hk : k < f
      · simp only [clI, hk, if_true, Idx.shift]; rw [if_neg (by omega)]
      · simp only [clI, hk, if_false, Idx.shift]
  | .add i j => by
      have h1 := clI_shift_id (ρ := ρ) hf i; have h2 := clI_shift_id (ρ := ρ) hf j
      simp only [clI]; revert h1 h2
      generalize clI ρ f i = a; generalize clI ρ f j = b
      intro h1 h2; cases a <;> cases b <;> simp_all [addF, Idx.shift]
  | .sub i j => by
      have h1 := clI_shift_id (ρ := ρ) hf i; have h2 := clI_shift_id (ρ := ρ) hf j
      simp only [clI]; revert h1 h2
      generalize clI ρ f i = a; generalize clI ρ f j = b
      intro h1 h2; cases a <;> cases b <;> simp_all [subF, Idx.shift]
  | .smul n i => by
      have h1 := clI_shift_id (ρ := ρ) hf i
      simp only [clI]; revert h1
      generalize clI ρ f i = a
      intro h1; cases a <;> simp_all [smulF, Idx.shift]

theorem clM_shift_id {ρ : Nat → Nat} {f c : Nat} (hf : f ≤ c) (μ : Mode) : (clM ρ f μ).shift c = clM ρ f μ := by
  cases μ <;> simp [clM, Mode.shift, clI_shift_id hf]

theorem cl_shiftI_id (ρ : Nat → Nat) : ∀ (t : Ty) (e f c : Nat), f ≤ c →
    (cl ρ (fun _ => .unit) e f t).shiftI c = cl ρ (fun _ => .unit) e f t := by
  intro t
  induction t with
  | intS i => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | prod a b iha ihb => intro e f c hf; simp [cl, Ty.shiftI, iha e f c hf, ihb e f c hf]
  | sum a b iha ihb => intro e f c hf; simp [cl, Ty.shiftI, iha e f c hf, ihb e f c hf]
  | code a b iha ihb => intro e f c hf; simp [cl, Ty.shiftI, iha e f c hf, ihb e f c hf]
  | array i t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e f c hf, clI_shift_id hf]
  | ptr μ t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e f c hf, clM_shift_id hf]
  | ptrOpt μ t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e f c hf, clM_shift_id hf]
  | loc μ t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e f c hf, clM_shift_id hf]
  | word r P => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | tok r st => intro e f c hf; cases st <;> simp [cl, Ty.shiftI, clI_shift_id hf]
  | word2 r P => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | tok2 r P i j => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | epair r P => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | tokE r P i => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | share r => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | cap s r => intro e f c hf; simp [cl, Ty.shiftI, clI_shift_id hf]
  | tvar k => intro e f c hf; simp only [cl]; split <;> rfl
  | mu t ih => intro e f c hf; simp [cl, Ty.shiftI, ih (e + 1) f c hf]
  | tex κ t ih => intro e f c hf; simp [cl, Ty.shiftI, ih (e + 1) f c hf]
  | iall t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e (f + 1) (c + 1) (by omega)]
  | iex t ih => intro e f c hf; simp [cl, Ty.shiftI, ih e (f + 1) (c + 1) (by omega)]
  | refine t ψ ih =>
      intro e f c hf
      simp only [cl, Ty.shiftI, ih e f c hf, Ty.refine.injEq, true_and]
      induction ψ with
      | tt => rfl
      | le i j => simp [clP, Pred.shift, clI_shift_id hf]
      | eq i j => simp [clP, Pred.shift, clI_shift_id hf]
      | and p q ihp ihq => simp only [clP, Pred.shift, ihp, ihq]
      | ini i => simp [clP, Pred.shift, clI_shift_id hf]
  | _ => intro e f c hf; rfl

theorem Clo_shiftI {s : Ty} (hs : Clo s) (c : Nat) : s.shiftI c = s := by
  have h := hs.2 (fun _ => 0) (fun _ => .unit) 0 0
  calc s.shiftI c = (cl (fun _ => 0) (fun _ => .unit) 0 0 s).shiftI c := by rw [h]
    _ = cl (fun _ => 0) (fun _ => .unit) 0 0 s := cl_shiftI_id _ s 0 0 c (Nat.zero_le _)
    _ = s := h

theorem ZRel_shiftIN {σ T : Ty} (hT : Clo T) (h : ZRel [] σ T) :
    ∀ (env : IEnv), ZRel env (shiftIN env.length σ) T := by
  intro env
  induction h' : env.length generalizing env with
  | zero => have : env = [] := List.eq_nil_of_length_eq_zero h'; subst this; exact h
  | succ n ih =>
      have h1 := ih (env.drop 1) (by simp [h'])
      have h2 := ZRel_shiftI _ (EnvSh.drop env) h1
      rw [Clo_shiftI hT] at h2; exact h2

theorem LocZ_shiftIN {σ T : Ty} (hT : Clo T) (h : LocZ [] σ T) :
    ∀ (env : IEnv), LocZ env (shiftIN env.length σ) T := by
  intro env
  induction h' : env.length generalizing env with
  | zero => have : env = [] := List.eq_nil_of_length_eq_zero h'; subst this; exact h
  | succ n ih =>
      have h1 := ih (env.drop 1) (by simp [h'])
      have h2 := LocZ_shiftI (EnvSh.drop env) h1
      rw [Clo_shiftI hT] at h2; exact h2

/-! ### Closing keeps what is known -/

theorem evalIn_addF (env : IEnv) (a b : Idx) : (addF a b).evalIn env = (Idx.add a b).evalIn env := by
  cases a <;> cases b <;> simp [addF, Idx.evalIn]

theorem evalIn_subF (env : IEnv) (a b : Idx) : (subF a b).evalIn env = (Idx.sub a b).evalIn env := by
  cases a <;> cases b <;> simp [subF, Idx.evalIn]

theorem evalIn_smulF (env : IEnv) (n : Nat) (a : Idx) : (smulF n a).evalIn env = (Idx.smul n a).evalIn env := by
  cases a <;> simp [smulF, Idx.evalIn]

/-- Under the `d` binders crossed (`env` has exactly their entries), closing
an index keeps every value it has. -/
theorem evalIn_clI {d : Nat} {ρ : Nat → Nat} {env : IEnv} (hd : env.length = d) : ∀ i : Idx, IdxLe env i (clI ρ d i)
  | .lit _ => fun _ h => h
  | .var k => by
      intro v h
      by_cases hk : k < d
      · simp only [clI, hk, if_true]; exact h
      · simp only [Idx.evalIn] at h
        rw [List.getElem?_eq_none (by omega)] at h; cases h
  | .add i j => by
      intro v h
      simp only [clI, evalIn_addF]
      simp only [Idx.evalIn] at h ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at h
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at h
          | some b => rw [evalIn_clI hd i a hi, evalIn_clI hd j b hj]; simpa [hi, hj] using h
  | .sub i j => by
      intro v h
      simp only [clI, evalIn_subF]
      simp only [Idx.evalIn] at h ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at h
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at h
          | some b => rw [evalIn_clI hd i a hi, evalIn_clI hd j b hj]; simpa [hi, hj] using h
  | .smul n i => by
      intro v h
      simp only [clI, evalIn_smulF]
      simp only [Idx.evalIn] at h ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at h
      | some a => rw [evalIn_clI hd i a hi]; simpa [hi] using h

theorem zeroHolds_clP {d : Nat} {ρ : Nat → Nat} {env : IEnv} (hd : env.length = d) :
    ∀ ψ : Pred, ψ.zeroHolds env = true → (clP ρ d ψ).zeroHolds env = true
  | .tt => fun h => h
  | .le i j => by
      intro h; simp only [clP, Pred.zeroHolds] at h ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at h
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at h
          | some b => rw [evalIn_clI hd i a hi, evalIn_clI hd j b hj]; simpa [hi, hj] using h
  | .eq i j => by
      intro h; simp only [clP, Pred.zeroHolds] at h ⊢
      cases hi : i.evalIn env with
      | none => simp [hi] at h
      | some a =>
          cases hj : j.evalIn env with
          | none => simp [hi, hj] at h
          | some b => rw [evalIn_clI hd i a hi, evalIn_clI hd j b hj]; simpa [hi, hj] using h
  | .and p q => by
      intro h; simp only [clP, Pred.zeroHolds, Bool.and_eq_true] at h ⊢
      exact ⟨zeroHolds_clP hd p h.1, zeroHolds_clP hd q h.2⟩
  | .ini i => by
      intro h; simp only [clP, Pred.zeroHolds, beq_iff_eq] at h ⊢
      exact evalIn_clI hd i 0 h

/-! ### The two renditions of a type agree on zeros -/

/-- A null `Loc`'s pointee: needs only that every type argument agrees on
its head (`hL`); `opq` arguments are `Unit`, which asks nothing. -/
theorem locZ_close_cl (σs : List Ty) (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ k, Clo (W k))
    (hL : ∀ k σ, σs[k]? = some σ → LocZ [] σ (W k)) (t : Ty) (c : Nat) (env : IEnv) :
    LocZ env (substTs σs c env.length t) (cl ρ W c env.length t) := by
  cases t with
  | tvar j =>
      simp only [substTs, cl]
      by_cases hj : j < c
      · simp only [hj, if_true, LocZ]
      · simp only [hj, if_false]
        cases hσ : σs[j - c]? with
        | none => simp only [LocZ]
        | some σ => exact LocZ_shiftIN (hW _) (LocZ_shiftTN c (hL _ σ hσ)) env
  | array i u => simp only [substTs, cl, LocZ]; exact evalIn_clI rfl i
  | _ => simp only [substTs, cl, LocZ] <;> trivial

/-- **Zero agreement of the two renditions**: closing a type by the runtime
type arguments (`substTs`) and by the witnesses (`cl`) agree on zeros,
provided every unguarded variable has an argument that agrees with its
witness, and every argument agrees with its witness on a `Loc`'s head. -/
theorem zrel_close_cl (σs : List Ty) (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ k, Clo (W k))
    (hL : ∀ k σ, σs[k]? = some σ → LocZ [] σ (W k)) :
    ∀ (t : Ty) (c : Nat) (env : IEnv),
      (∀ k, t.guardT (c + k) = false → ∃ σ, σs[k]? = some σ ∧ ZRel [] σ (W k)) →
      ZRel env (substTs σs c env.length t) (cl ρ W c env.length t) := by
  intro t
  induction t with
  | tvar j =>
      intro c env H
      simp only [substTs, cl]
      by_cases hj : j < c
      · simp only [hj, if_true, ZRel]
      · obtain ⟨k, rfl⟩ : ∃ k, j = c + k := ⟨j - c, by omega⟩
        obtain ⟨σ, hσ, hz⟩ := H k (by simp [Ty.guardT])
        have e : c + k - c = k := by omega
        simp only [hj, if_false, e, hσ]
        exact ZRel_shiftIN (hW _) (ZRel_shiftTN c c hz) env
  | intS i => intro c env _; simp only [substTs, cl, ZRel]; exact evalIn_clI rfl i
  | prod a b iha ihb =>
      intro c env H
      exact ⟨iha c env (fun k hk => H k (by simp [Ty.guardT, hk])),
        ihb c env (fun k hk => H k (by simp [Ty.guardT, hk]))⟩
  | sum a b iha ihb =>
      intro c env H
      exact ⟨iha c env (fun k hk => H k (by simp [Ty.guardT, hk])),
        ihb c env (fun k hk => H k (by simp [Ty.guardT, hk]))⟩
  | array i t ih =>
      intro c env H
      exact ⟨evalIn_clI rfl i, ih c env (fun k hk => H k (by simpa [Ty.guardT] using hk))⟩
  | loc μ t _ => intro c env _; exact locZ_close_cl σs ρ W hW hL t c env
  | mu t ih =>
      intro c env H
      exact ih (c + 1) env (fun k hk => H k (by
        have e : c + 1 + k = c + k + 1 := by omega
        rw [e] at hk; simpa [Ty.guardT] using hk))
  | tex κ t ih =>
      intro c env H
      exact ih (c + 1) env (fun k hk => H k (by
        have e : c + 1 + k = c + k + 1 := by omega
        rw [e] at hk; simpa [Ty.guardT] using hk))
  | iall t ih =>
      intro c env H
      exact ih c (none :: env) (fun k hk => H k (by simpa [Ty.guardT] using hk))
  | iex t ih =>
      intro c env H
      exact ih c (some 0 :: env) (fun k hk => H k (by simpa [Ty.guardT] using hk))
  | refine t ψ ih =>
      intro c env H
      exact ⟨ih c env (fun k hk => H k (by simpa [Ty.guardT] using hk)), zeroHolds_clP rfl ψ⟩
  | _ => intro c env _; simp only [substTs, cl, ZRel]

/-- Zero agreement of a frame's type arguments with its witnesses; an `opq`
argument is `Unit` (`unpackT`), which a `Loc` head never needs. -/
def ZWit (σs : List Ty) (W : Nat → Ty) (opq : List Nat) : Prop :=
  ∀ k σ, σs[k]? = some σ → (k ∉ opq → ZRel [] σ (W k)) ∧ (k ∈ opq → σ = .unit)

/-- **Layout agreement** of a frame: its runtime type arguments `σs` and its
witnesses `W` agree in `sig` at every type variable in range and outside `opq`
(the variables `unpackT` bound, where `σs` has `Unit` for the erased
witness).  Out of range the two cannot agree (`close` leaves a variable, a
witness is closed), so a type must keep its unguarded variables in range.
T3c-5b adds zero agreement (`ZWit`); T3c-5c adds layout (`accs`) agreement, which
`sig` agreement alone does not give (coupling counts index mentions). -/
def WitL (σs : List Ty) (W : Nat → Ty) (opq : List Nat) : Prop :=
  (∀ k, k ∉ opq → k < σs.length → sig (close σs (.tvar k)) = sig (W k)) ∧ ZWit σs W opq ∧
    (∀ k, k ∉ opq → k < σs.length → accs (close σs (.tvar k)) = accs (W k))

/-- A type whose `opq` variables occur only under references (`Cx.opaqueOK`)
and whose other unguarded variables are in range has the same `sig` in both
renditions. -/
theorem sig_WitL {σs : List Ty} {W : Nat → Ty} {opq : List Nat} (h : WitL σs W opq) (ρ : Nat → Nat)
    {t : Ty} (hg : opq.all (fun k => t.guardT k) = true)
    (hr : ∀ k, t.guardT k = false → k < σs.length) : sig (close σs t) = sig (cl ρ W 0 0 t) := by
  refine sig_close_cl σs ρ W t 0 0 (fun k hk => ?_)
  simp only [Nat.zero_add] at hk
  refine h.1 k (fun hm => ?_) (hr k hk)
  have := List.all_eq_true.1 hg k hm
  rw [hk] at this; cases this

/-- The same type, under the same conditions, agrees on zeros in both
renditions. -/
theorem zrel_WitL {σs : List Ty} {W : Nat → Ty} {opq : List Nat} (h : WitL σs W opq)
    (hC : ∀ k, Clo (W k)) (ρ : Nat → Nat) {t : Ty} (hg : opq.all (fun k => t.guardT k) = true)
    (hr : ∀ k, t.guardT k = false → k < σs.length) : ZRel [] (close σs t) (cl ρ W 0 0 t) := by
  refine zrel_close_cl σs ρ W hC (fun k σ hσ => ?_) t 0 [] (fun k hk => ?_)
  · by_cases hm : k ∈ opq
    · rw [(h.2.1 k σ hσ).2 hm]; trivial
    · exact ZRel_loc ((h.2.1 k σ hσ).1 hm)
  · simp only [Nat.zero_add] at hk
    have hm : k ∉ opq := fun hm => by
      have := List.all_eq_true.1 hg k hm
      rw [hk] at this; cases this
    have hl := hr k hk
    exact ⟨σs[k], List.getElem?_eq_getElem hl, (h.2.1 k σs[k] (List.getElem?_eq_getElem hl)).1 hm⟩

theorem skel_eq_code {rt a b : Ty} (h : skel rt = .code a b) :
    ∃ ra rb, rt = .code ra rb ∧ skel ra = a ∧ skel rb = b := by
  cases rt with
  | code ra rb => simp only [skel, Ty.code.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem eskel_eq_code {rt a b : Ty} (h : etok (skel rt) = .code a b) :
    ∃ ra rb, rt = .code ra rb ∧ etok (skel ra) = a ∧ etok (skel rb) = b := by
  cases rt with
  | code ra rb => simp only [skel, etok, Ty.code.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

/-- Subsumption only grows arms (`Ptr ≤ Ptr?`) and keeps sum heads. -/
theorem sub_arms {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat),
    ArmsLe (armsOf (substTs σs c d σ)) (armsOf (substTs σs c d τ)) ∧
    sumHead (substTs σs c d σ) = sumHead (substTs σs c d τ) := by
  induction h with
  | eq h =>
      intro σs c d
      have e := skel_subst_eq (skel_tyEq h) σs c d d
      exact ⟨arms_of_skel e, sumHead_of_skel e⟩
  | intS => intro σs c d; exact ⟨.cons (ArmLe.of_info rfl) .nil, rfl⟩
  | refine _ ih => intro σs c d; simpa only [substTs, armsOf, sumHead] using ih σs c d
  | iniWeak h _ =>
      intro σs c d
      have e := skel_subst_eq (skel_tyEq h) σs c d d
      simp only [substTs, armsOf, sumHead]
      exact ⟨arms_of_skel e, sumHead_of_skel e⟩
  | nonNull =>
      intro σs c d
      refine ⟨.cons ⟨Or.inr ⟨?_, ?_⟩, rfl⟩ .nil, rfl⟩ <;>
        simp [substTs, armK, info, Arms.ptrArm, Arms.optArm]
  | prod ha hb _ _ =>
      intro σs c d
      have e := (info_sub (SubS.prod ha hb) σs c d).1
      refine ⟨.cons (ArmLe.of_info ?_) .nil, rfl⟩
      simp only [substTs, info, Info.leaf] at e ⊢
      rw [e]
  | sum _ _ iha ihb =>
      intro σs c d
      simp only [substTs, armsOf, sumHead]
      exact ⟨(iha σs c d).1.append (ihb σs c d).1, by trivial⟩
  | cap => intro σs c d; exact ⟨.cons (ArmLe.of_info rfl) .nil, rfl⟩

/-- **Subsumption keeps runtime validity** (after any type substitution). -/
theorem Valid_sub {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat) (ws : List Word),
    Valid (substTs σs c d σ) ws → Valid (substTs σs c d τ) ws := by
  induction h with
  | eq h => intro σs c d ws hv; exact Valid_of_skel (skel_subst_eq (skel_tyEq h) σs c d d) hv
  | intS => intro σs c d ws _; trivial
  | refine _ ih => intro σs c d ws hv; exact ih σs c d ws hv
  | iniWeak h _ =>
      intro σs c d ws hv
      simp only [substTs, Valid] at hv ⊢
      exact Valid_of_skel (skel_subst_eq (skel_tyEq h) σs c d d) hv
  | nonNull => intro σs c d ws hv; exact Or.inr hv
  | prod ha hb iha ihb =>
      intro σs c d ws hv n hn
      rw [← wc_sub ha] at hn
      obtain ⟨h1, h2⟩ := hv n hn
      exact ⟨iha σs c d _ h1, ihb σs c d _ h2⟩
  | sum ha hb iha ihb =>
      intro σs c d ws hv
      exact SumV_mono (info_sub (SubS.sum ha hb) σs c d).tier (sub_arms ha σs c d).1 (sub_arms hb σs c d).1
        (sub_arms ha σs c d).2 (sub_arms hb σs c d).2 (info_sub ha σs c d).tier (info_sub hb σs c d).tier
        (wc_sub ha σs c d) (wc_sub hb σs c d) (iha σs c d) (ihb σs c d) hv
  | cap => intro σs c d ws _; trivial

theorem ShapeC_len {rt : Ty} {ws : List Word} {n : Nat} (hs : ShapeC rt ws) (hn : wc rt = some n) :
    ws.length = n := by
  obtain ⟨us, hu, rfl⟩ := wc_some hn; exact hs us hu

/-! ## Layout forms (`lyt`)

`skel` forgets every index, so two runtime types with one skeleton can have
different layouts: a package is coupled when two of its words mention its
bound index (`countI`), and `skel` cannot see that.  `lyt d` keeps exactly what
`accs` reads at every depth, pointees included: the shape, and of each index
term only which of the `d` innermost (bound) index variables it mentions.
Free indices and refinements over them are forgotten, as `skel` forgets them,
so integer re-typing and index equalities at depth 0 do not change it. -/

/-- The variables below `d` that `m` holds, as one index term. -/
def ofMs (m : Nat → Bool) : Nat → Idx
  | 0 => .lit 0
  | n + 1 => if m n then .add (.var n) (ofMs m n) else ofMs m n

theorem ofMs_mentions (m : Nat → Bool) (k : Nat) :
    ∀ d, (ofMs m d).mentions k = (decide (k < d) && m k)
  | 0 => by simp [ofMs, Idx.mentions]
  | n + 1 => by
      have ih := ofMs_mentions m k n
      by_cases h : m n
      · simp only [ofMs, h, ite_true, Idx.mentions, ih]
        by_cases hk : k = n
        · subst hk; simp [h]
        · have h1 : (n == k) = false := by simp; omega
          rw [h1]; by_cases hk2 : k < n
          · simp [hk2, show k < n + 1 by omega]
          · simp [hk2, show ¬ k < n + 1 by omega]
      · simp only [ofMs, if_neg h]; rw [ih]
        by_cases hk : k = n
        · subst hk; simp [h]
        · by_cases hk2 : k < n
          · simp [hk2, show k < n + 1 by omega]
          · simp [hk2, show ¬ k < n + 1 by omega]

theorem ofMs_congr {m m' : Nat → Bool} : ∀ {d}, (∀ k, k < d → m k = m' k) → ofMs m d = ofMs m' d
  | 0, _ => rfl
  | n + 1, h => by
      simp only [ofMs]; rw [h n (by omega), ofMs_congr (fun k hk => h k (by omega))]

/-- The canonical form of an index term below depth `d`. -/
def idxC (d : Nat) (i : Idx) : Idx := ofMs (fun k => i.mentions k) d

theorem idxC_mentions {d k : Nat} (i : Idx) (h : k < d) : (idxC d i).mentions k = i.mentions k := by
  simp [idxC, ofMs_mentions, h]

def modeC (d : Nat) : Mode → Mode
  | .rgn r => .rgn (idxC d r)
  | μ => μ

theorem modeC_mentions {d k : Nat} (μ : Mode) (h : k < d) : (modeC d μ).mentions k = μ.mentions k := by
  cases μ <;> simp [modeC, Mode.mentions, idxC_mentions _ h]

/-- Does `ψ` mention a variable below `d`? -/
def anyB (m : Nat → Bool) (d : Nat) : Bool := (List.range d).any m

theorem anyB_false {m : Nat → Bool} {d : Nat} (h : anyB m d = false) : ∀ k, k < d → m k = false := by
  intro k hk
  simp only [anyB, List.any_eq_false, List.mem_range] at h
  simpa using h k hk

/-- **Layout form** below `d` index binders. -/
def lyt (d : Nat) : Ty → Ty
  | .int => .intS (.lit 0)
  | .intS i => .intS (idxC d i)
  | .prod a b => .prod (lyt d a) (lyt d b)
  | .sum a b => .sum (lyt d a) (lyt d b)
  | .code a b => .code (lyt d a) (lyt d b)
  | .array i t => .array (idxC d i) (lyt d t)
  | .ptr μ t => .ptr (modeC d μ) (lyt d t)
  | .ptrOpt μ t => .ptrOpt (modeC d μ) (lyt d t)
  | .loc μ t => .loc (modeC d μ) (lyt d t)
  | .word r P => .word (idxC d r) P
  | .tok r st => .tok (idxC d r) (st.map fun (P, i) => (P, idxC d i))
  | .word2 r P => .word2 (idxC d r) P
  | .tok2 r P i j => .tok2 (idxC d r) P (idxC d i) (idxC d j)
  | .epair r P => .epair (idxC d r) P
  | .tokE r P i => .tokE (idxC d r) P (idxC d i)
  | .share r => .share (idxC d r)
  | .cap s r => .cap s (idxC d r)
  | .mu t => .mu (lyt d t)
  | .tex κ t => .tex κ (lyt d t)
  | .iall t => .iall (lyt (d + 1) t)
  | .iex t => .iex (lyt (d + 1) t)
  | .refine t ψ =>
      if anyB (fun k => ψ.mentions k) d then .refine (lyt d t) (.ini (ofMs (fun k => ψ.mentions k) d))
      else lyt d t
  | t => t

theorem lyt_idxMentions : ∀ (t : Ty) (d k : Nat), k < d → (lyt d t).idxMentions k = t.idxMentions k := by
  intro t
  induction t with
  | iall t ih => intro d k hk; simp only [lyt, Ty.idxMentions]; exact ih (d + 1) (k + 1) (by omega)
  | iex t ih => intro d k hk; simp only [lyt, Ty.idxMentions]; exact ih (d + 1) (k + 1) (by omega)
  | refine t ψ ih =>
      intro d k hk
      simp only [lyt]
      split
      · simp only [Ty.idxMentions, ih d k hk, Pred.mentions, ofMs_mentions, hk, decide_true, Bool.true_and]
      · rename_i h
        simp only [Ty.idxMentions, ih d k hk, anyB_false (Bool.eq_false_iff.2 h) k hk, Bool.or_false]
  | tok r st =>
      intro d k hk
      cases st with
      | none => simp [lyt, Ty.idxMentions, idxC_mentions _ hk]
      | some p => obtain ⟨P, i⟩ := p; simp [lyt, Ty.idxMentions, idxC_mentions _ hk]
  | _ => intro d k hk; simp_all [lyt, Ty.idxMentions, idxC_mentions _ hk, modeC_mentions _ hk, Idx.mentions]

theorem lyt_tyMentions : ∀ (t : Ty) (d k : Nat), (lyt d t).tyMentions k = t.tyMentions k := by
  intro t
  induction t with
  | refine t ψ ih => intro d k; simp only [lyt]; split <;> simp [Ty.tyMentions, ih]
  | tok r st => intro d k; simp [lyt, Ty.tyMentions]
  | _ => intro d k; simp_all [lyt, Ty.tyMentions]

theorem lyt_countT : ∀ (t : Ty) (d k : Nat), (lyt d t).countT k = t.countT k := by
  intro t
  induction t with
  | refine t ψ ih => intro d k; simp only [lyt]; split <;> simp [Ty.countT, ih]
  | mu t ih => intro d k; simp [lyt, Ty.countT, ih, lyt_tyMentions]
  | tok r st => intro d k; simp [lyt, Ty.countT, Ty.tyMentions]
  | _ => intro d k; simp_all [lyt, Ty.countT, lyt_tyMentions, Ty.tyMentions] <;> split <;> simp_all

theorem lyt_countI : ∀ (t : Ty) (d k : Nat), k < d → (lyt d t).countI k = t.countI k := by
  intro t
  induction t with
  | iall t ih => intro d k hk; simp only [lyt, Ty.countI]; exact ih (d + 1) (k + 1) (by omega)
  | iex t ih => intro d k hk; simp only [lyt, Ty.countI]; exact ih (d + 1) (k + 1) (by omega)
  | refine t ψ ih =>
      intro d k hk
      simp only [lyt]
      split
      · simp only [Ty.countI, ih d k hk, Pred.mentions, ofMs_mentions, hk, decide_true, Bool.true_and]
      · rename_i h
        simp only [Ty.countI, ih d k hk, anyB_false (Bool.eq_false_iff.2 h) k hk]; simp
  | mu t ih => intro d k hk; simp [lyt, Ty.countI, ih d k hk, lyt_idxMentions t d k hk, lyt_countT]
  | tex κ t ih => intro d k hk; simp [lyt, Ty.countI, ih d k hk]
  | prod a b iha ihb => intro d k hk; simp [lyt, Ty.countI, iha d k hk, ihb d k hk]
  | tok r st =>
      intro d k hk
      cases st with
      | none => simp [lyt, Ty.countI, Ty.idxMentions, idxC_mentions _ hk]
      | some p => obtain ⟨P, i⟩ := p; simp [lyt, Ty.countI, Ty.idxMentions, idxC_mentions _ hk]
  | _ =>
      intro d k hk
      simp_all [lyt, Ty.countI, Ty.idxMentions, idxC_mentions _ hk, modeC_mentions _ hk,
        lyt_idxMentions _ d k hk, Idx.mentions] <;> split <;> simp_all

theorem lyt_info : ∀ (t : Ty) (d : Nat) (ρ : Ctx), info ρ (lyt d t) = info ρ t := by
  intro t
  induction t with
  | refine t ψ ih => intro d ρ; simp only [lyt]; split <;> simp [info, ih]
  | tok r st => intro d ρ; simp [lyt, info]
  | _ => intro d ρ; simp_all [lyt, info]

theorem lyt_width (t : Ty) (d : Nat) : (lyt d t).width = t.width := by
  simp only [Ty.width, lyt_info]

theorem lyt_tier (t : Ty) (d : Nat) : (lyt d t).tier = t.tier := by
  simp only [Ty.tier, lyt_info]

theorem lyt_rawWords (t : Ty) (d : Nat) : (lyt d t).rawWords = t.rawWords := by
  simp only [Ty.rawWords, lyt_width]

/-- **A layout form determines the layout.** -/
theorem accs_lyt : ∀ (t : Ty) (d : Nat), accs (lyt d t) = accs t := by
  intro t
  induction t with
  | prod a b iha ihb => intro d; simp [lyt, accs, iha, ihb]
  | sum a b iha ihb =>
      intro d
      have := lyt_tier (.sum a b) d
      simp only [lyt] at this
      simp only [lyt, accs, this]
  | refine t ψ ih => intro d; simp only [lyt]; split <;> simp [accs, ih]
  | iall t ih => intro d; simp [lyt, accs, ih]
  | mu t ih => intro d; simp [lyt, accs, ih]
  | iex t ih =>
      intro d
      have hr := lyt_rawWords (.iex t) d
      simp only [lyt] at hr
      simp only [lyt, accs, ih, lyt_countI t (d + 1) 0 (by omega), hr]
  | tex κ t ih =>
      intro d
      have hr := lyt_rawWords (.tex κ t) d
      simp only [lyt] at hr
      simp only [lyt, accs, ih, lyt_countT, hr]
  | tok r st => intro d; simp [lyt, accs]
  | _ => intro d; simp [lyt, accs]

theorem accs_of_lyt {a b : Ty} {d : Nat} (h : lyt d a = lyt d b) : accs a = accs b := by
  rw [← accs_lyt a d, h, accs_lyt]

/-- (T3d-1) Token erasure commutes with layout forms: a token's layout form is
a token, erased either way; `etok` stops at the binders `lyt` counts under. -/
theorem etok_lyt : ∀ (t : Ty) (d : Nat), etok (lyt d t) = lyt d (etok t) := by
  intro t
  induction t with
  | prod a b iha ihb => intro d; simp only [etok, lyt, iha, ihb]
  | sum a b iha ihb => intro d; simp only [etok, lyt, iha, ihb]
  | code a b iha ihb => intro d; simp only [etok, lyt, iha, ihb]
  | array i t ih => intro d; simp only [etok, lyt, ih]
  | ptr μ t ih => intro d; simp only [etok, lyt, ih]
  | ptrOpt μ t ih => intro d; simp only [etok, lyt, ih]
  | loc μ t ih => intro d; simp only [etok, lyt, ih]
  | refine t ψ ih => intro d; simp only [etok, lyt]; split <;> simp only [etok, ih]
  | _ => intro d; rfl

theorem accs_of_elyt {a b : Ty} {d : Nat} (h : etok (lyt d a) = etok (lyt d b)) : accs a = accs b := by
  rw [← accs_etok a, ← accs_lyt (etok a) d, ← etok_lyt, h, etok_lyt, accs_lyt, accs_etok]

theorem elyt_of_lyt {a b : Ty} {d : Nat} (h : lyt d a = lyt d b) : etok (lyt d a) = etok (lyt d b) := by rw [h]

/-! ### Layout forms under shifts and substitutions -/

theorem ms_shift_self (c : Nat) : ∀ i : Idx, (i.shift c).mentions c = false
  | .lit _ => rfl
  | .var k' => by
      by_cases h : k' ≥ c
      · simp only [Idx.shift, h, ite_true, Idx.mentions]; simp; omega
      · simp only [Idx.shift, h, ite_false, Idx.mentions]; simp; omega
  | .add i j => by simp only [Idx.shift, Idx.mentions, ms_shift_self c i, ms_shift_self c j]; rfl
  | .sub i j => by simp only [Idx.shift, Idx.mentions, ms_shift_self c i, ms_shift_self c j]; rfl
  | .smul _ i => by simp only [Idx.shift, Idx.mentions, ms_shift_self c i]

theorem ms_shift_succ (c k : Nat) (hk : c ≤ k) : ∀ i : Idx, (i.shift c).mentions (k + 1) = i.mentions k
  | .lit _ => rfl
  | .var k' => by
      by_cases h : k' ≥ c
      · simp only [Idx.shift, h, ite_true, Idx.mentions]; simp
      · simp only [Idx.shift, h, ite_false, Idx.mentions]
        rw [show (k' == k + 1) = false by simp; omega, show (k' == k) = false by simp; omega]
  | .add i j => by simp only [Idx.shift, Idx.mentions, ms_shift_succ c k hk i, ms_shift_succ c k hk j]
  | .sub i j => by simp only [Idx.shift, Idx.mentions, ms_shift_succ c k hk i, ms_shift_succ c k hk j]
  | .smul _ i => by simp only [Idx.shift, Idx.mentions, ms_shift_succ c k hk i]

theorem pms_shift_self (c : Nat) : ∀ ψ : Pred, (ψ.shift c).mentions c = false
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.mentions, ms_shift_self]; rfl
  | .eq i j => by simp only [Pred.shift, Pred.mentions, ms_shift_self]; rfl
  | .and p q => by simp only [Pred.shift, Pred.mentions, pms_shift_self c p, pms_shift_self c q]; rfl
  | .ini i => by simp only [Pred.shift, Pred.mentions, ms_shift_self]

theorem pms_shift_succ (c k : Nat) (hk : c ≤ k) : ∀ ψ : Pred, (ψ.shift c).mentions (k + 1) = ψ.mentions k
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.mentions, ms_shift_succ c k hk]
  | .eq i j => by simp only [Pred.shift, Pred.mentions, ms_shift_succ c k hk]
  | .and p q => by simp only [Pred.shift, Pred.mentions, pms_shift_succ c k hk p, pms_shift_succ c k hk q]
  | .ini i => by simp only [Pred.shift, Pred.mentions, ms_shift_succ c k hk]

theorem mms_shift_self (c : Nat) (μ : Mode) : (μ.shift c).mentions c = false := by
  cases μ <;> simp [Mode.shift, Mode.mentions, ms_shift_self]

theorem mms_shift_succ (c k : Nat) (hk : c ≤ k) (μ : Mode) : (μ.shift c).mentions (k + 1) = μ.mentions k := by
  cases μ <;> simp [Mode.shift, Mode.mentions, ms_shift_succ c k hk]

theorem idxMentions_shiftI_self : ∀ (t : Ty) (c : Nat), (t.shiftI c).idxMentions c = false := by
  intro t
  induction t with
  | tok r i => intro c; rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, Ty.idxMentions, ms_shift_self]
  | iall t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1)]
  | iex t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1)]
  | _ => intro c; simp_all [Ty.shiftI, Ty.idxMentions, ms_shift_self, mms_shift_self, pms_shift_self]

theorem idxMentions_shiftI_succ : ∀ (t : Ty) (c k : Nat), c ≤ k →
    (t.shiftI c).idxMentions (k + 1) = t.idxMentions k := by
  intro t
  induction t with
  | tok r i => intro c k hk; rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, Ty.idxMentions, ms_shift_succ c k hk]
  | iall t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | iex t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | _ => intro c k hk; simp_all [Ty.shiftI, Ty.idxMentions, ms_shift_succ c k hk, mms_shift_succ c k hk,
      pms_shift_succ c k hk]

theorem idxMentions_shiftIN : ∀ (n : Nat) (t : Ty) (k : Nat), k < n → (shiftIN n t).idxMentions k = false
  | 0, _, _, h => absurd h (by omega)
  | n + 1, t, k, h => by
      simp only [shiftIN]
      rcases k with _ | k
      · exact idxMentions_shiftI_self _ 0
      · rw [idxMentions_shiftI_succ _ 0 k (by omega)]; exact idxMentions_shiftIN n t k (by omega)

/-! Generic facts about `ofMs` and `anyB`. -/

theorem ofMs_succ_false {m : Nat → Bool} {n : Nat} (h : m n = false) : ofMs m (n + 1) = ofMs m n := by
  simp [ofMs, h]

theorem anyB_succ (m : Nat → Bool) (n : Nat) : anyB m (n + 1) = (anyB m n || m n) := by
  simp [anyB, List.range_succ, List.any_append]

theorem anyB_congr {m m' : Nat → Bool} : ∀ {d : Nat}, (∀ k, k < d → m k = m' k) → anyB m d = anyB m' d
  | 0, _ => rfl
  | n + 1, h => by rw [anyB_succ, anyB_succ, h n (by omega), anyB_congr (fun k hk => h k (by omega))]

theorem anyB_succ_false {m : Nat → Bool} {n : Nat} (h : m n = false) : anyB m (n + 1) = anyB m n := by
  simp [anyB, List.range_succ, List.any_append, h]

theorem anyB_zero (m : Nat → Bool) : anyB m 0 = false := by simp [anyB]

theorem anyB_mono {m : Nat → Bool} {d d' : Nat} (hd : d' ≤ d) (h : anyB m d' = true) : anyB m d = true := by
  simp only [anyB, List.any_eq_true, List.mem_range] at h ⊢
  obtain ⟨k, hk, hm⟩ := h; exact ⟨k, by omega, hm⟩

/-- The pointwise shape of a shift at `e` past a gap `[e, D)`. -/
theorem gap_ms {m m' : Nat → Bool} {e D : Nat} (he : e ≤ D) (hlt : ∀ k, k < e → m' k = m k)
    (hself : m' e = false) (hsucc : ∀ k, e ≤ k → m' (k + 1) = m k)
    (hI : ∀ k, e ≤ k → k < D → m k = false) : ∀ k, k < D + 1 → m' k = (decide (k < D) && m k) := by
  intro k hk
  rcases Nat.lt_or_ge k e with h | h
  · rw [hlt k h]; simp [show k < D by omega]
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'; rw [hself]
      by_cases hD : e < D
      · simp [hD, hI e (Nat.le_refl e) hD]
      · simp [hD]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [hsucc k' (by omega), hI k' (by omega) (by omega)]; simp
      intro hh; exact hI _ (by omega) hh

theorem ofMs_gap {m m' : Nat → Bool} {D : Nat} (h : ∀ k, k < D + 1 → m' k = (decide (k < D) && m k)) :
    ofMs m' (D + 1) = ofMs m D := by
  rw [ofMs_congr (m := m') (m' := fun k => decide (k < D) && m k) h, ofMs_succ_false (by simp)]
  exact ofMs_congr (fun k hk => by simp [hk])

theorem anyB_gap {m m' : Nat → Bool} {D : Nat} (h : ∀ k, k < D + 1 → m' k = (decide (k < D) && m k)) :
    anyB m' (D + 1) = anyB m D := by
  rw [anyB_congr (m := m') (m' := fun k => decide (k < D) && m k) h, anyB_succ_false (by simp)]
  exact anyB_congr (fun k hk => by simp [hk])

theorem idxC_shift_ge {d c : Nat} (i : Idx) (h : d ≤ c) : idxC d (i.shift c) = idxC d i :=
  ofMs_congr (fun k hk => mentions_shift c k (by omega) i)

theorem modeC_shift_ge {d c : Nat} (μ : Mode) (h : d ≤ c) : modeC d (μ.shift c) = modeC d μ := by
  cases μ <;> simp [Mode.shift, modeC, idxC_shift_ge _ h]

theorem idxC_shift_gap {e D : Nat} (i : Idx) (he : e ≤ D) (hI : ∀ k, e ≤ k → k < D → i.mentions k = false) :
    idxC (D + 1) (i.shift e) = idxC D i :=
  ofMs_gap (gap_ms he (fun k hk => mentions_shift e k hk i) (ms_shift_self e i)
    (fun k hk => ms_shift_succ e k hk i) hI)

theorem modeC_shift_gap {e D : Nat} (μ : Mode) (he : e ≤ D) (hI : ∀ k, e ≤ k → k < D → μ.mentions k = false) :
    modeC (D + 1) (μ.shift e) = modeC D μ := by
  cases μ with
  | rgn r => simp only [Mode.shift, modeC]; rw [idxC_shift_gap r he hI]
  | _ => rfl

theorem orF {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := Bool.or_eq_false_iff.1 h

/-- **Index shifts at or above `d` leave `lyt d` alone.** -/
theorem lyt_shiftI_ge : ∀ (t : Ty) (c d : Nat), d ≤ c → lyt d (t.shiftI c) = lyt d t := by
  intro t
  induction t with
  | iall t ih => intro c d h; simp only [Ty.shiftI, lyt]; rw [ih (c + 1) (d + 1) (by omega)]
  | iex t ih => intro c d h; simp only [Ty.shiftI, lyt]; rw [ih (c + 1) (d + 1) (by omega)]
  | refine t ψ ih =>
      intro c d h
      have hm : ∀ k, k < d → (ψ.shift c).mentions k = ψ.mentions k :=
        fun k hk => pred_mentions_shift c k (by omega) ψ
      simp only [Ty.shiftI, lyt, ih c d h, anyB_congr (m := fun k => (ψ.shift c).mentions k) hm,
        ofMs_congr (m := fun k => (ψ.shift c).mentions k) hm]
  | tok r st =>
      intro c d h
      cases st with
      | none => simp [Ty.shiftI, lyt, idxC_shift_ge _ h]
      | some p => obtain ⟨P, i⟩ := p; simp [Ty.shiftI, lyt, idxC_shift_ge _ h]
  | _ => intro c d h; simp_all [Ty.shiftI, lyt, idxC_shift_ge _ h, modeC_shift_ge _ h]

/-- **A shift past an unmentioned gap `[e, D)` is absorbed by one more level.** -/
theorem lyt_shiftI_gap : ∀ (t : Ty) (e D : Nat), e ≤ D → (∀ k, e ≤ k → k < D → t.idxMentions k = false) →
    lyt (D + 1) (t.shiftI e) = lyt D t := by
  intro t
  induction t with
  | intS i => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap i he hI]
  | prod a b iha ihb =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | sum a b iha ihb =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | code a b iha ihb =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | array i t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, idxC_shift_gap i he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | ptr μ t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, modeC_shift_gap μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | ptrOpt μ t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, modeC_shift_gap μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | loc μ t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt, modeC_shift_gap μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | word r P => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap r he hI]
  | word2 r P => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap r he hI]
  | tok2 r P i j =>
      intro e D he hI
      simp only [Ty.idxMentions] at hI
      simp [Ty.shiftI, lyt, idxC_shift_gap r he (fun k h1 h2 => (orF (orF (hI k h1 h2)).1).1),
        idxC_shift_gap i he (fun k h1 h2 => (orF (orF (hI k h1 h2)).1).2),
        idxC_shift_gap j he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | epair r P => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap r he hI]
  | tokE r P i =>
      intro e D he hI
      simp only [Ty.idxMentions] at hI
      simp [Ty.shiftI, lyt, idxC_shift_gap r he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        idxC_shift_gap i he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | share r => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap r he hI]
  | cap s r => intro e D he hI; simp only [Ty.shiftI, lyt, idxC_shift_gap r he hI]
  | tok r st =>
      intro e D he hI
      cases st with
      | none =>
          simp only [Ty.idxMentions, Option.any_none, Bool.or_false] at hI
          simp [Ty.shiftI, lyt, idxC_shift_gap r he hI]
      | some p =>
          obtain ⟨P, i⟩ := p
          simp only [Ty.idxMentions, Option.any_some] at hI
          simp [Ty.shiftI, lyt, idxC_shift_gap r he (fun k h1 h2 => (orF (hI k h1 h2)).1),
            idxC_shift_gap i he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | mu t ih => intro e D he hI; simp only [Ty.shiftI, lyt, ih e D he hI]
  | tex κ t ih => intro e D he hI; simp only [Ty.shiftI, lyt, ih e D he hI]
  | iall t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt]
      rw [ih (e + 1) (D + 1) (by omega) (fun k h1 h2 => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hI k' (by omega) (by omega))]
  | iex t ih =>
      intro e D he hI
      simp only [Ty.shiftI, lyt]
      rw [ih (e + 1) (D + 1) (by omega) (fun k h1 h2 => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hI k' (by omega) (by omega))]
  | refine t ψ ih =>
      intro e D he hI
      have hg := gap_ms (m := fun k => ψ.mentions k) (m' := fun k => (ψ.shift e).mentions k) he
        (fun k hk => pred_mentions_shift e k hk ψ) (pms_shift_self e ψ)
        (fun k hk => pms_shift_succ e k hk ψ) (fun k h1 h2 => (orF (hI k h1 h2)).2)
      simp only [Ty.shiftI, lyt, ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).1), anyB_gap hg, ofMs_gap hg]
  | _ => intros; rfl

theorem lyt_shiftIN : ∀ (n : Nat) (t : Ty), lyt n (shiftIN n t) = lyt 0 t
  | 0, _ => rfl
  | n + 1, t => by
      simp only [shiftIN]
      rw [lyt_shiftI_gap _ 0 n (by omega) (fun k _ hk => idxMentions_shiftIN n t k hk)]
      exact lyt_shiftIN n t

theorem ofMs_shift {c : Nat} (m : Nat → Bool) : ∀ {e}, e ≤ c → (ofMs m e).shift c = ofMs m e
  | 0, _ => rfl
  | n + 1, h => by
      have ih := ofMs_shift (c := c) m (e := n) (by omega)
      by_cases hm : m n
      · simp only [ofMs, hm, ite_true, Idx.shift, ih]; simp; omega
      · simp only [ofMs, hm]; simpa using ih

/-- A layout form below `e` mentions nothing at or above `e`. -/
theorem lyt_shiftI_id : ∀ (t : Ty) (e c : Nat), e ≤ c → (lyt e t).shiftI c = lyt e t := by
  intro t
  induction t with
  | iall t ih => intro e c h; simp only [lyt, Ty.shiftI]; rw [ih (e + 1) (c + 1) (by omega)]
  | iex t ih => intro e c h; simp only [lyt, Ty.shiftI]; rw [ih (e + 1) (c + 1) (by omega)]
  | refine t ψ ih =>
      intro e c h
      simp only [lyt]
      split
      · simp only [Ty.shiftI, ih e c h, Pred.shift, idxC, ofMs_shift _ h]
      · exact ih e c h
  | ptr μ t ih => intro e c h; cases μ <;> simp [lyt, modeC, Ty.shiftI, Mode.shift, idxC, ofMs_shift _ h, ih e c h]
  | ptrOpt μ t ih => intro e c h; cases μ <;> simp [lyt, modeC, Ty.shiftI, Mode.shift, idxC, ofMs_shift _ h, ih e c h]
  | loc μ t ih => intro e c h; cases μ <;> simp [lyt, modeC, Ty.shiftI, Mode.shift, idxC, ofMs_shift _ h, ih e c h]
  | tok r st =>
      intro e c h
      cases st with
      | none => simp [lyt, Ty.shiftI, idxC, ofMs_shift _ h]
      | some p => obtain ⟨P, i⟩ := p; simp [lyt, Ty.shiftI, idxC, ofMs_shift _ h]
  | _ => intro e c h; simp_all [lyt, Ty.shiftI, idxC, ofMs_shift _ h, Idx.shift]

theorem shiftIN_lyt0 : ∀ (n : Nat) (t : Ty), shiftIN n (lyt 0 t) = lyt 0 t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftIN, shiftIN_lyt0 n t, lyt_shiftI_id t 0 0 (Nat.le_refl 0)]

theorem lyt_shiftT : ∀ (t : Ty) (c d : Nat), lyt d (t.shiftT c) = (lyt d t).shiftT c := by
  intro t
  induction t with
  | refine t ψ ih => intro c d; simp only [Ty.shiftT, lyt]; split <;> simp_all [Ty.shiftT]
  | tok r st => intro c d; simp [lyt, Ty.shiftT]
  | tvar k => intro c d; simp only [Ty.shiftT, lyt]; split <;> simp [lyt]
  | _ => intro c d; simp_all [Ty.shiftT, lyt]

theorem lyt_shiftTN (d : Nat) : ∀ (n : Nat) (t : Ty), lyt d (shiftTN n t) = shiftTN n (lyt d t)
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftTN, lyt_shiftT, lyt_shiftTN d n t]

theorem ofMs_gap2 {m : Nat → Bool} {e : Nat} : ∀ {D : Nat}, e ≤ D → (∀ k, e ≤ k → k < D → m k = false) →
    ofMs m D = ofMs m e
  | 0, h, _ => by have : e = 0 := by omega
                  subst this; rfl
  | D + 1, h, hI => by
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; rfl
      · rw [ofMs_succ_false (hI D (by omega) (by omega))]
        exact ofMs_gap2 (by omega) (fun k h1 h2 => hI k h1 (by omega))

theorem anyB_gap2 {m : Nat → Bool} {e : Nat} : ∀ {D : Nat}, e ≤ D → (∀ k, e ≤ k → k < D → m k = false) →
    anyB m D = anyB m e
  | 0, h, _ => by have : e = 0 := by omega
                  subst this; rfl
  | D + 1, h, hI => by
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · subst h'; rfl
      · rw [anyB_succ_false (hI D (by omega) (by omega))]
        exact anyB_gap2 (by omega) (fun k h1 h2 => hI k h1 (by omega))

theorem idxC_gap2 {e D : Nat} (i : Idx) (he : e ≤ D) (hI : ∀ k, e ≤ k → k < D → i.mentions k = false) :
    idxC D i = idxC e i := ofMs_gap2 he hI

theorem modeC_gap2 {e D : Nat} (μ : Mode) (he : e ≤ D) (hI : ∀ k, e ≤ k → k < D → μ.mentions k = false) :
    modeC D μ = modeC e μ := by
  cases μ with
  | rgn r => simp only [modeC]; rw [idxC_gap2 r he hI]
  | _ => rfl

/-- **Unmentioned levels `[e, D)` do not matter.** -/
theorem lyt_gap2 : ∀ (t : Ty) (e D : Nat), e ≤ D → (∀ k, e ≤ k → k < D → t.idxMentions k = false) →
    lyt D t = lyt e t := by
  intro t
  induction t with
  | intS i => intro e D he hI; simp only [lyt, idxC_gap2 i he hI]
  | prod a b iha ihb =>
      intro e D he hI
      simp only [lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | sum a b iha ihb =>
      intro e D he hI
      simp only [lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | code a b iha ihb =>
      intro e D he hI
      simp only [lyt, iha e D he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ihb e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | array i t ih =>
      intro e D he hI
      simp only [lyt, idxC_gap2 i he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | ptr μ t ih =>
      intro e D he hI
      simp only [lyt, modeC_gap2 μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | ptrOpt μ t ih =>
      intro e D he hI
      simp only [lyt, modeC_gap2 μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | loc μ t ih =>
      intro e D he hI
      simp only [lyt, modeC_gap2 μ he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | word r P => intro e D he hI; simp only [lyt, idxC_gap2 r he hI]
  | word2 r P => intro e D he hI; simp only [lyt, idxC_gap2 r he hI]
  | tok2 r P i j =>
      intro e D he hI
      simp only [Ty.idxMentions] at hI
      simp [lyt, idxC_gap2 r he (fun k h1 h2 => (orF (orF (hI k h1 h2)).1).1),
        idxC_gap2 i he (fun k h1 h2 => (orF (orF (hI k h1 h2)).1).2),
        idxC_gap2 j he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | epair r P => intro e D he hI; simp only [lyt, idxC_gap2 r he hI]
  | tokE r P i =>
      intro e D he hI
      simp only [Ty.idxMentions] at hI
      simp [lyt, idxC_gap2 r he (fun k h1 h2 => (orF (hI k h1 h2)).1),
        idxC_gap2 i he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | share r => intro e D he hI; simp only [lyt, idxC_gap2 r he hI]
  | cap s r => intro e D he hI; simp only [lyt, idxC_gap2 r he hI]
  | tok r st =>
      intro e D he hI
      cases st with
      | none =>
          simp only [Ty.idxMentions, Option.any_none, Bool.or_false] at hI
          simp [lyt, idxC_gap2 r he hI]
      | some p =>
          obtain ⟨P, i⟩ := p
          simp only [Ty.idxMentions, Option.any_some] at hI
          simp [lyt, idxC_gap2 r he (fun k h1 h2 => (orF (hI k h1 h2)).1),
            idxC_gap2 i he (fun k h1 h2 => (orF (hI k h1 h2)).2)]
  | mu t ih => intro e D he hI; simp only [lyt, ih e D he hI]
  | tex κ t ih => intro e D he hI; simp only [lyt, ih e D he hI]
  | iall t ih =>
      intro e D he hI
      simp only [lyt]
      rw [ih (e + 1) (D + 1) (by omega) (fun k h1 h2 => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hI k' (by omega) (by omega))]
  | iex t ih =>
      intro e D he hI
      simp only [lyt]
      rw [ih (e + 1) (D + 1) (by omega) (fun k h1 h2 => by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        exact hI k' (by omega) (by omega))]
  | refine t ψ ih =>
      intro e D he hI
      have hg : ∀ k, e ≤ k → k < D → (fun k => ψ.mentions k) k = false := fun k h1 h2 => (orF (hI k h1 h2)).2
      simp only [lyt, ih e D he (fun k h1 h2 => (orF (hI k h1 h2)).1), anyB_gap2 he hg, ofMs_gap2 he hg]
  | _ => intros; rfl

theorem lyt_shiftIN_le {d n : Nat} (t : Ty) (h : d ≤ n) : lyt d (shiftIN n t) = lyt 0 t := by
  rw [lyt_gap2 _ 0 d (Nat.zero_le _) (fun k _ hk => idxMentions_shiftIN n t k (by omega)),
    ← lyt_gap2 _ 0 n (Nat.zero_le _) (fun k _ hk => idxMentions_shiftIN n t k hk), lyt_shiftIN]

/-- **`lyt` commutes with type substitution**, the substituted types taken to
their depth-0 layout forms; the substitution may run deeper than `lyt`. -/
theorem lyt_substTs : ∀ (t : Ty) (σs : List Ty) (c d d' : Nat), d ≤ d' →
    lyt d (substTs σs c d' t) = substTs (σs.map (lyt 0)) c d (lyt d t) := by
  intro t
  induction t with
  | tvar k =>
      intro σs c d d' hd
      simp only [substTs, lyt]
      by_cases hk : k < c
      · simp [hk, lyt]
      · simp only [hk, ite_false, List.getElem?_map]
        cases h : σs[k - c]? with
        | none => simp [lyt]
        | some σ => simp only [Option.map_some]; rw [lyt_shiftIN_le _ hd, ← lyt_shiftTN, shiftIN_lyt0]
  | iall t ih => intro σs c d d' hd; simp only [substTs, lyt]; rw [ih σs c (d + 1) (d' + 1) (by omega)]
  | iex t ih => intro σs c d d' hd; simp only [substTs, lyt]; rw [ih σs c (d + 1) (d' + 1) (by omega)]
  | refine t ψ ih => intro σs c d d' hd; simp only [substTs, lyt]; split <;> simp_all [substTs]
  | tok r st => intro σs c d d' hd; simp [lyt, substTs]
  | _ => intro σs c d d' hd; simp_all [substTs, lyt]

theorem lyt_close (σs : List Ty) (t : Ty) : lyt 0 (close σs t) = close (σs.map (lyt 0)) (lyt 0 t) :=
  lyt_substTs t σs 0 0 0 (Nat.le_refl 0)

/-- An integer type's layout form. -/
theorem lyt0_intOf {t : Ty} {o : Option Idx} (h : intOf t = some o) (σs : List Ty) (c d : Nat) :
    lyt 0 (substTs σs c d t) = .intS (.lit 0) := by
  induction t with
  | intS => rfl
  | int => rfl
  | refine t ψ ih => simp only [intOf] at h; simp only [substTs, lyt, anyB_zero, ih h]; rfl
  | _ => simp [intOf] at h

theorem substT_shiftI_unit : ∀ (t : Ty) (j c : Nat), Ty.substT j .unit (t.shiftI c) = (Ty.substT j .unit t).shiftI c := by
  intro t
  induction t with
  | tvar k => intro j c; simp only [Ty.shiftI, Ty.substT]; split <;> (try split) <;> rfl
  | _ => intro j c; simp_all [Ty.shiftI, Ty.substT, shiftT_unit, shiftI_unit]

theorem substT_shiftIN_unit (j : Nat) : ∀ (n : Nat) (t : Ty), Ty.substT j .unit (shiftIN n t) = shiftIN n (Ty.substT j .unit t)
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftIN, substT_shiftI_unit, substT_shiftIN_unit j n t]

theorem shiftIN_unit' : ∀ n, shiftIN n .unit = .unit
  | 0 => rfl
  | n + 1 => by simp only [shiftIN, shiftIN_unit' n]; rfl

theorem substT_substTs_unit (σs : List Ty) : ∀ (u : Ty) (c d : Nat),
    Ty.substT c .unit (substTs σs (c + 1) d u) = substTs (.unit :: σs) c d u := by
  intro u
  induction u with
  | tvar k =>
      intro c d
      rcases Nat.lt_trichotomy k c with h | rfl | h
      · have h1 : k < c + 1 := by omega
        have h2 : ¬ k > c := by omega
        have h3 : k ≠ c := by omega
        simp [substTs, Ty.substT, h, h1, h2, h3]
      · simp [substTs, Ty.substT, shiftTN_unit, shiftIN_unit']
      · obtain ⟨m, rfl⟩ : ∃ m, k = c + m + 1 := ⟨k - c - 1, by omega⟩
        have h1 : ¬ c + m + 1 < c + 1 := by omega
        have h5 : ¬ c + m + 1 < c := by omega
        have e1 : c + m + 1 - (c + 1) = m := by omega
        have e2 : c + m + 1 - c = m + 1 := by omega
        simp only [substTs, h1, h5, e1, e2, if_false, List.getElem?_cons_succ, List.length_cons]
        cases hm : σs[m]? with
        | some τ =>
            simp only
            rw [substT_shiftIN_unit, ← shiftT_shiftTN c c τ (Nat.le_refl _), substT_shiftT]
        | none =>
            have hl : σs.length ≤ m := by simpa using hm
            have h6 : c + m + 1 - σs.length ≠ c := by omega
            have h7 : c + m + 1 - σs.length > c := by omega
            simp only
            rw [show Ty.substT c .unit (.tvar (c + m + 1 - σs.length)) = .tvar (c + m + 1 - σs.length - 1) by
              simp [Ty.substT, h6, h7]]
            exact congrArg Ty.tvar (by omega)
  | mu t ih => intro c d; simp only [substTs, Ty.substT, shiftT_unit, ih]
  | tex κ t ih => intro c d; simp only [substTs, Ty.substT, shiftT_unit, ih]
  | iall t ih => intro c d; simp only [substTs, Ty.substT, shiftI_unit, ih]
  | iex t ih => intro c d; simp only [substTs, Ty.substT, shiftI_unit, ih]
  | _ => intro c d; simp_all [substTs, Ty.substT]

theorem lyt_substT_unit : ∀ (t : Ty) (j d : Nat), lyt d (Ty.substT j .unit t) = Ty.substT j .unit (lyt d t) := by
  intro t
  induction t with
  | tvar k => intro j d; simp only [Ty.substT]; split <;> (try split) <;> simp [lyt, Ty.substT, *]
  | mu t ih => intro j d; simp only [Ty.substT, lyt, shiftT_unit, ih]
  | tex κ t ih => intro j d; simp only [Ty.substT, lyt, shiftT_unit, ih]
  | iall t ih => intro j d; simp only [Ty.substT, lyt, shiftI_unit, ih]
  | iex t ih => intro j d; simp only [Ty.substT, lyt, shiftI_unit, ih]
  | refine t ψ ih => intro j d; simp only [Ty.substT, lyt]; split <;> simp_all [Ty.substT]
  | tok r st => intro j d; simp [lyt, Ty.substT]
  | _ => intro j d; simp_all [Ty.substT, lyt]

theorem idxC_idxC {d d' : Nat} (i : Idx) (h : d' ≤ d) : idxC d' (idxC d i) = idxC d' i :=
  ofMs_congr (fun k hk => idxC_mentions i (by omega))

theorem modeC_modeC {d d' : Nat} (μ : Mode) (h : d' ≤ d) : modeC d' (modeC d μ) = modeC d' μ := by
  cases μ <;> simp [modeC, idxC_idxC _ h]

theorem ofMs_ff : ∀ n, ofMs (fun _ => false) n = .lit 0
  | 0 => rfl
  | n + 1 => by simp [ofMs, ofMs_ff n]

theorem idxC_lit (d n : Nat) : idxC d (.lit n) = .lit 0 := by
  simp only [idxC, Idx.mentions]; exact ofMs_ff d

/-- **Coarsening**: `lyt d'` after `lyt d` is `lyt d'`, for `d' ≤ d`. -/
theorem lyt_down : ∀ (t : Ty) (d d' : Nat), d' ≤ d → lyt d' (lyt d t) = lyt d' t := by
  intro t
  induction t with
  | iall t ih => intro d d' h; simp only [lyt]; rw [ih (d + 1) (d' + 1) (by omega)]
  | iex t ih => intro d d' h; simp only [lyt]; rw [ih (d + 1) (d' + 1) (by omega)]
  | refine t ψ ih =>
      intro d d' h
      have hm : ∀ k, k < d' → (Pred.ini (ofMs (fun k => ψ.mentions k) d)).mentions k = ψ.mentions k := by
        intro k hk; simp [Pred.mentions, ofMs_mentions, show k < d by omega]
      by_cases ha : anyB (fun k => ψ.mentions k) d = true
      · simp only [lyt, ha, ite_true, anyB_congr hm, ofMs_congr hm, ih d d' h]
      · have ha' : anyB (fun k => ψ.mentions k) d' = false := by
          cases e : anyB (fun k => ψ.mentions k) d'
          · rfl
          · exact absurd (anyB_mono h e) ha
        simp only [lyt, ha, ha']
        first | exact ih d d' h | (simp; exact ih d d' h)
  | tok r st =>
      intro d d' h
      cases st with
      | none => simp [lyt, idxC_idxC _ h]
      | some p => obtain ⟨P, i⟩ := p; simp [lyt, idxC_idxC _ h]
  | _ => intro d d' h; simp_all [lyt, idxC_idxC _ h, modeC_modeC _ h, idxC_lit]

/-- The runtime side of a binding of static type `t`: the words fit the runtime
layout, which exists, and the runtime type has the skeleton of `t` closed by
the frame's type arguments `σs` (§2d) — up to token erasure (`etok`, T3d-1
option 1b): the runtime binds `Unit` where a `cas`, a `claim` or a Keep store
binds a token, and a token has no words. -/
def Lay (σs : List Ty) (t rt : Ty) (ws : List Word) : Prop :=
  ShapeC rt ws ∧ etok (skel rt) = etok (skel (close σs t)) ∧ wc rt ≠ none ∧ Valid rt ws ∧
    etok (lyt 0 rt) = etok (lyt 0 (close σs t))

/-- A static token, epoch token or share is `Unit` with no words at runtime. -/
theorem Lay_etok_unit {σs : List Ty} {t : Ty} (h : etok t = .unit) : Lay σs t .unit [] := by
  refine ⟨fun us hv => by simp [accs] at hv; subst hv; rfl, ?_, by simp [wc, accs], trivial, ?_⟩ <;>
    cases t <;> simp_all [etok, close, substTs, skel, lyt]

theorem Lay_shiftI {σs : List Ty} {t rt : Ty} {ws : List Word} (c : Nat) (h : Lay σs t rt ws) :
    Lay σs (t.shiftI c) rt ws :=
  ⟨h.1, by rw [skel_close_shiftI]; exact h.2.1, h.2.2.1, h.2.2.2.1,
    by rw [lyt_close, lyt_shiftI_ge t c 0 (Nat.zero_le _), ← lyt_close]; exact h.2.2.2.2⟩

/-- An integer result: runtime `Int`, one word. -/
theorem Lay_int {σs : List Ty} {t : Ty} {o : Option Idx} (w : Word) (h : intOf t = some o) :
    Lay σs t .int [w] :=
  ⟨shape_int w, by unfold close; rw [skel_intOf h σs 0 0]; rfl, by simp [wc, accs], trivial,
    by unfold close; rw [lyt0_intOf h σs 0 0]; rfl⟩

/-- Integer re-typing (`nameI`) keeps the runtime side. -/
theorem Lay_retype {σs : List Ty} {t t' rt : Ty} {o o' : Option Idx} {ws : List Word}
    (h : intOf t = some o) (h' : intOf t' = some o') (hl : Lay σs t rt ws) : Lay σs t' rt ws :=
  ⟨hl.1, by rw [hl.2.1]; unfold close; rw [skel_intOf h, skel_intOf h'], hl.2.2.1, hl.2.2.2.1,
    by rw [hl.2.2.2.2]; unfold close; rw [lyt0_intOf h, lyt0_intOf h']⟩

theorem Lay_fix (σs : List Ty) (sg : Bool) (w : Wd) (x : Word) : Lay σs (.fix sg w) (.fix sg w) [x] :=
  ⟨shape_fix sg w x, rfl, by simp [wc, accs], trivial, rfl⟩

theorem Lay_lanes (σs : List Ty) (sg : Bool) (w : Wd) (x : Word) :
    Lay σs (.lanes sg w) (.lanes sg w) [x] :=
  ⟨shape_lanes sg w x, rfl, by simp [wc, accs], trivial, rfl⟩

theorem Lay_pair {σs : List Ty} {t u rt ru : Ty} {ws us : List Word} (ha : Lay σs t rt ws)
    (hb : Lay σs u ru us) : Lay σs (.prod t u) (.prod rt ru) (ws ++ us) := by
  refine ⟨fun vs hv => ?_, ?_, ?_, ?_, ?_⟩
  · cases h1 : accs rt <;> cases h2 : accs ru <;> simp [accs, h1, h2] at hv
    subst hv
    rw [List.length_append, ha.1 _ h1, hb.1 _ h2, nWords_append]
  · show Ty.prod (etok (skel rt)) (etok (skel ru)) = Ty.prod (etok (skel (close σs t))) (etok (skel (close σs u)))
    rw [ha.2.1, hb.2.1]
  · rw [wc_prod]
    cases h1 : wc rt with
    | none => exact absurd h1 ha.2.2.1
    | some n =>
        cases h2 : wc ru with
        | none => exact absurd h2 hb.2.2.1
        | some m => simp
  · intro n hn
    have hl := ShapeC_len ha.1 hn
    subst hl
    simp only [List.take_left, List.drop_left]
    exact ⟨ha.2.2.2.1, hb.2.2.2.1⟩
  · show Ty.prod (etok (lyt 0 rt)) (etok (lyt 0 ru)) = Ty.prod (etok (lyt 0 (close σs t))) (etok (lyt 0 (close σs u)))
    rw [ha.2.2.2.2, hb.2.2.2.2]

/-- Every static variable has a runtime binding whose words realise its type
and whose runtime type lays them out as the static type says. -/
def VarsOK (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (vars : List (String × Ty × Bool)) (env : Env) : Prop :=
  ∀ x e, vars.find? (·.1 == x) = some e →
    ∃ rt ws, lookupE env x = some (rt, ws) ∧ VR ρ η e.2.1 (shp rt) ws ∧ Lay σs e.2.1 rt ws

/-- The frame's return continuation `K` accepts every value the frame may
return: one realising the static return type `ret`, laid out at its closed
rendition `close σs ret` (the caller rebinds it there, F2),
(T3c-4b) at any extension `η'` of the frame's view — Σ may have grown by the
time the frame returns — and `K` is told the thread-wide part `CE η'`. -/
def RetOK (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (ret : Ty) (K : TEnv → List Word → Prop) : Prop :=
  ∀ η', Ext η η' → ∀ ws, VR ρ η' ret (shp (close σs ret)) ws → Lay σs ret (close σs ret) ws → K (CE η') ws

/-- A kind's `copy` keeps a protocol word out (a word is affine), so it
implies what `noWord` asks. -/
theorem ask_mono {ke : KEnv} {k : Nat} {r : Bool} {f g : Kind → Bool} (h : ke.ask k r f = true)
    (hfg : ∀ κ, f κ = true → g κ = true) : ke.ask k r g = true := by
  revert h; unfold KEnv.ask; split <;> simp_all

/-- Not affine implies not a protocol word at the head. -/
theorem wordFreeIn_of_affine {ke : KEnv} : ∀ u : Ty, Ty.affineIn ke u = false → Ty.wordFreeIn ke u = true := by
  intro u
  induction u with
  | tvar k =>
      intro h
      simp only [Ty.affineIn, Bool.not_eq_false'] at h
      simp only [Ty.wordFreeIn]
      exact ask_mono h (fun κ hc => by simp [hc])
  | refine t ψ ih => intro h; simp only [Ty.affineIn] at h; simp only [Ty.wordFreeIn]; exact ih h
  | word r P => intro h; simp [Ty.affineIn] at h
  | word2 r P => intro h; simp [Ty.affineIn] at h
  | epair r P => intro h; simp [Ty.affineIn] at h
  | _ => intro _; simp [Ty.wordFreeIn]

/-- (T3c-5b) A type variable whose kind says `Zeroable` has a runtime type
argument that is `Zeroable`: what `newBuf` needs to make its `ini` promise. -/
def KindsZ (ke : KEnv) (σs : List Ty) : Prop :=
  ∀ k, ke.ask k false (·.zero) = true → ∃ σ, σs[k]? = some σ ∧ zeroableIn [] [] σ = true

theorem accs_ne_iex (t : Ty) : accs (.iex t) ≠ none ↔ accs t ≠ none := by
  constructor
  · intro h ht
    rcases accs_iex t with e | ⟨k, hr, _⟩
    · exact h (e.trans ht)
    · obtain ⟨w0, hw, _⟩ := rawWords_iex hr
      rw [accs_none_width t ht] at hw; cases hw
  · intro h h'
    rcases accs_iex t with e | ⟨k, _, hm⟩
    · exact h (e.symm.trans h')
    · simp [h'] at hm

theorem accs_ne_tex (κ : Kind) (t : Ty) : accs (.tex κ t) ≠ none ↔ accs t ≠ none := by
  constructor
  · intro h ht
    rcases accs_tex κ t with e | ⟨k, hr, _⟩
    · exact h (e.trans ht)
    · obtain ⟨w0, hw, _⟩ := rawWords_tex hr
      rw [accs_none_width t ht] at hw; cases hw
  · intro h h'
    rcases accs_tex κ t with e | ⟨k, _, hm⟩
    · exact h (e.symm.trans h')
    · simp [h'] at hm

theorem accs_ne_prod (a b : Ty) : accs (.prod a b) ≠ none ↔ accs a ≠ none ∧ accs b ≠ none := by
  cases ha : accs a <;> cases hb : accs b <;> simp [accs, ha, hb]

theorem accs_shiftIN : ∀ (n : Nat) (t : Ty), accs (shiftIN n t) = accs t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftIN, accs_shiftI, accs_shiftIN n t]

theorem accs_shiftTN_ne (n : Nat) (t : Ty) (h : accs t ≠ none) : accs (shiftTN n t) ≠ none := by
  have hw : wc (shiftTN n t) = wc t := wc_of_sig (sig_shiftTN n t)
  simp only [wc] at hw
  intro h'; rw [h'] at hw; cases ht : accs t
  · exact h ht
  · rw [ht] at hw; cases hw

/-- (T3c-5b) **Substituting laid-out type arguments keeps a layout**: a
well-formed, array-free type whose variables below `c` are guarded (they are
`μ`/`∃α` binders crossed on the way) has one once its free variables are
replaced by type arguments that have one. -/
theorem accs_substTs {σs : List Ty} (hσ : ∀ σ ∈ σs, accs σ ≠ none) :
    ∀ (t : Ty) (c d nt ni : Nat), t.wf nt ni = true → t.arrFree = true →
      (∀ k, k < c → t.unguarded k = false) → nt ≤ c + σs.length →
      accs (substTs σs c d t) ≠ none := by
  intro t
  induction t with
  | tvar k =>
      intro c d nt ni hwf _ hg hn
      simp only [Ty.wf, decide_eq_true_eq] at hwf
      by_cases hk : k < c
      · have := hg k hk; simp [Ty.unguarded] at this
      · simp only [substTs, hk, ite_false]
        have hl : k - c < σs.length := by omega
        rw [List.getElem?_eq_getElem hl]
        simp only
        rw [accs_shiftIN]
        exact accs_shiftTN_ne c _ (hσ _ (List.getElem_mem hl))
  | prod a b iha ihb =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree, Bool.and_eq_true] at hwf haf
      simp only [substTs]
      rw [accs_ne_prod]
      have hg' : ∀ k, k < c → a.unguarded k = false ∧ b.unguarded k = false := by
        intro k hk; have := hg k hk; simp only [Ty.unguarded, Bool.or_eq_false_iff] at this; exact this
      exact ⟨iha c d nt ni hwf.1 haf.1 (fun k hk => (hg' k hk).1) hn,
        ihb c d nt ni hwf.2 haf.2 (fun k hk => (hg' k hk).2) hn⟩
  | sum a b _ _ =>
      intro c d nt ni _ _ _ _
      simp only [substTs, accs]; split <;> simp
  | word r P =>
      intro c d nt ni _ _ _ _
      simp only [substTs, accs]; split <;> simp
  | array i t _ =>
      intro c d nt ni _ haf _ _; simp [Ty.arrFree] at haf
  | mu t ih =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree, Bool.and_eq_true, Bool.not_eq_true'] at hwf haf
      simp only [substTs, accs]
      refine ih (c + 1) d (nt + 1) ni hwf.2 haf (fun k hk => ?_) (by omega)
      cases k with
      | zero => exact hwf.1
      | succ j => have := hg j (by omega); simpa [Ty.unguarded] using this
  | tex κ t ih =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree, Bool.and_eq_true, Bool.not_eq_true'] at hwf haf
      simp only [substTs]
      rw [accs_ne_tex]
      refine ih (c + 1) d (nt + 1) ni hwf.2 haf (fun k hk => ?_) (by omega)
      cases k with
      | zero => exact hwf.1
      | succ j => have := hg j (by omega); simpa [Ty.unguarded] using this
  | iall t ih =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree] at hwf haf
      simp only [substTs, accs]
      exact ih c (d + 1) nt (ni + 1) hwf haf (fun k hk => by simpa [Ty.unguarded] using hg k hk) hn
  | iex t ih =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree] at hwf haf
      simp only [substTs]
      rw [accs_ne_iex]
      exact ih c (d + 1) nt (ni + 1) hwf haf (fun k hk => by simpa [Ty.unguarded] using hg k hk) hn
  | refine t ψ ih =>
      intro c d nt ni hwf haf hg hn
      simp only [Ty.wf, Ty.arrFree, Bool.and_eq_true] at hwf haf
      simp only [substTs, accs]
      exact ih c d nt ni hwf.2 haf (fun k hk => by simpa [Ty.unguarded] using hg k hk) hn
  | _ => intros; simp [substTs, accs]

/-- **Closing at laid-out type arguments keeps a layout.** -/
theorem accs_close {σs : List Ty} {τ : Ty} {nt ni : Nat} (hwf : τ.wf nt ni = true)
    (hn : nt ≤ σs.length) (haf : τ.arrFree = true) (hσ : ∀ σ ∈ σs, accs σ ≠ none) :
    accs (close σs τ) ≠ none :=
  accs_substTs hσ τ 0 0 nt ni hwf haf (fun _ hk => absurd hk (Nat.not_lt_zero _)) (by omega)

/-- (T3c-5b) **Every type argument has a layout**: so does what the frame
closes at them (`accs_close`), which is what `newBuf` allocates. -/
def KindsL (σs : List Ty) : Prop := ∀ σ ∈ σs, accs σ ≠ none

/-- **The frame's type arguments respect its kinds**, as far as protocol words
go: a type variable whose kind says `noWord` or `copy` (the cases where
`wordFreeIn` answers `true` from the kind) has a word-free runtime argument.
`unpackT`'s erased witness is `Unit`, which is word-free. -/
def KindsOK (ke : KEnv) (σs : List Ty) : Prop :=
  (∀ k, ke.ask k true (fun κ => κ.noWord || κ.copy) = true → ∃ σ, σs[k]? = some σ ∧ Ty.wordFree σ = true) ∧
  KindsZ ke σs ∧ KindsL σs

/-- What the checker concluded is `Zeroable`, closed at the frame's type
arguments, is `Zeroable` (`KindSound.zero_close`).  A hypothesis here because
KindSound comes after this file. -/
def ZeroCloseP : Prop :=
  ∀ (ke : KEnv) (σs : List Ty) (σ : Ty), KindsZ ke σs → zeroableIn [] ke σ = true →
    zeroableIn [] [] (close σs σ) = true

/-- What the checker concluded is word-free, closed at the frame's type
arguments, is word-free. -/
theorem wordFree_close {ke : KEnv} {σs : List Ty} (hK : KindsOK ke σs) :
    ∀ u : Ty, Ty.wordFreeIn ke u = true → Ty.wordFree (close σs u) = true := by
  intro u
  induction u with
  | tvar k =>
      intro h
      obtain ⟨σ, hσ, hw⟩ := hK.1 k h
      simp only [close, substTs, Nat.not_lt_zero, if_false, Nat.sub_zero, hσ]
      exact hw
  | refine t ψ ih =>
      intro h; simp only [Ty.wordFreeIn] at h
      simp only [close, substTs, Ty.wordFree, Ty.wordFreeIn] at ih ⊢; exact ih h
  | word r P => intro h; simp [Ty.wordFreeIn] at h
  | word2 r P => intro h; simp [Ty.wordFreeIn] at h
  | epair r P => intro h; simp [Ty.wordFreeIn] at h
  | _ => intro _; simp [close, substTs, Ty.wordFree, Ty.wordFreeIn]

theorem wordOf_ptr_of_wordFree {μ : Mode} {σ : Ty} (h : Ty.wordFree σ = true) : wordOf (.ptr μ σ) = none := by
  cases σ <;> simp_all [wordOf, Ty.wordFree, Ty.wordFreeIn]

theorem KindsOK_pushT {ke : KEnv} {σs : List Ty} (κ : Kind) (hK : KindsOK ke σs) :
    KindsOK (some κ :: ke) (.unit :: σs) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun σ hσ => ?_⟩
  · cases k with
    | zero => exact ⟨.unit, rfl, rfl⟩
    | succ j =>
        obtain ⟨σ, h1, h2⟩ := hK.1 j (by unfold KEnv.ask at hk ⊢; simpa using hk)
        exact ⟨σ, by simpa using h1, h2⟩
  · cases k with
    | zero => exact ⟨.unit, rfl, by simp [zeroableIn]⟩
    | succ j =>
        obtain ⟨σ, h1, h2⟩ := hK.2.1 j (by unfold KEnv.ask at hk ⊢; simpa using hk)
        exact ⟨σ, by simpa using h1, h2⟩
  · rcases List.mem_cons.1 hσ with rfl | h
    · simp [accs]
    · exact hK.2.2 σ h

/-- (T3c-5a) **No witness holds an array by value**: type arguments are
admitted (`admitsIn` asks `arrFree`), and so are package witnesses (`packT`).
So a bound variable's type, closed, is `arrFree`: a `null` locative (whose
pointee closes to an array) is never loaded through. -/
def WitAF (η : TEnv) : Prop :=
  ∀ k, (η.wit k).arrFree = true ∧ noIallV (η.wit k) = true ∧ TermTv.mg (η.wit k) = true

theorem WitAF.af {η : TEnv} (h : WitAF η) : ∀ k, (η.wit k).arrFree = true := fun k => (h k).1

theorem WitAF.ni {η : TEnv} (h : WitAF η) : ∀ k, noIallV (η.wit k) = true := fun k => (h k).2.1

/-- (GStoMg) The witnesses' `μ` bodies are guarded. -/
theorem WitAF.mg {η : TEnv} (h : WitAF η) : ∀ k, TermTv.mg (η.wit k) = true := fun k => (h k).2.2

#print axioms WitAF.mg

/-- (T3c-5c) **Share witnesses are `coupledOK`**: a type variable whose kind says `share` stands
for a witness that passes `coupledOK` (`admitsIn` checks it at `pack` and at instantiation), so
`coupledOK` survives closing (`coupledOK_cl`). -/
def WitSh (ke : KEnv) (η : TEnv) : Prop := ∀ k, ke.ask k true (·.share) = true → Ty.coupledOK (η.wit k) = true

/-- (P3) Copy-kinded type variables' witnesses are not affine: a copied value
holds no resource. -/
def WitC (ke : KEnv) (η : TEnv) : Prop := ∀ k, ke.ask k true (·.copy) = true → Ty.affine (η.wit k) = false

/-- (B.3) The witnesses of `noOwn` variables reach no `own` reference: what makes
a published cell's type (a closure) `noOwn`. -/
def WitN (ke : KEnv) (η : TEnv) : Prop := ∀ k, ke.ask k true (·.noOwn) = true → Ty.noOwn (η.wit k) = true

/-- (S7) `share` witnesses are region-free (until R2): the scope checks every
type argument (`call`, `tail`) and every `share` package witness (`packT`). -/
def WitR (ke : KEnv) (η : TEnv) : Prop := ∀ k, ke.ask k true (·.share) = true → rgnFree (η.wit k) = true

/-- (P3) Under `WitC` and `CohR`, copy-kinded variables denote resource-free
values: the hypotheses of `VRR_copy_zero`. -/
theorem WitC_zero {ke : KEnv} {η : TEnv} (hw : WitC ke η) (hr : CohR η) :
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.rrs k S vs Y → Y = .zero) ∧
    (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.urrs k S vs Y → Y = .zero) := by
  have h0 : ∀ k, KEnv.ask [] k true (·.copy) = true → False := fun k h => by simp [KEnv.ask] at h
  refine ⟨fun k hk S vs Y h => ?_, fun k hk S vs Y h => ?_⟩
  · exact VRR_copy_zero _ [] _ _ _ _ _ (hw k hk) (fun k h => (h0 k h).elim) (fun k h => (h0 k h).elim)
      (((hr k).1 (fun _ => 0) S vs Y).1 h)
  · exact VRR_copy_zero _ [] _ _ _ _ _ (hw k hk) (fun k h => (h0 k h).elim) (fun k h => (h0 k h).elim)
      (((hr k).2 (fun _ => 0) S vs Y).1 h)

/-- (P3) A frame's non-affine values carry nothing. -/
theorem VRR_copy_frame {ke : KEnv} {η : TEnv} (hw : WitC ke η) (hr : CohR η) {t : Ty} {ρ : Nat → Nat}
    {rt : Shp} {ws : List Word} {X : Res} (ha : Ty.affineIn ke t = false) (hv : VRR ρ η t rt ws X) :
    X = .zero :=
  VRR_copy_zero t ke ρ η rt ws X ha (WitC_zero hw hr).1 (WitC_zero hw hr).2 hv

/-! ### Closing keeps `coupledOK` (T3c-5c; moved from KindSound: `countI_zero`, `countT_zero`) -/

theorem countI_zero : ∀ (t : Ty) (k : Nat), t.idxMentions k = false → t.countI k = 0 := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro k h; simp only [Ty.idxMentions, Bool.or_eq_false_iff] at h
      simp only [Ty.countI, iha k h.1, ihb k h.2]
  | refine t ψ ih =>
      intro k h; simp only [Ty.idxMentions, Bool.or_eq_false_iff] at h
      simp only [Ty.countI, ih k h.1, h.2]; rfl
  | iall t ih => intro k h; simp only [Ty.idxMentions] at h; simp only [Ty.countI, ih (k + 1) h]
  | iex t ih => intro k h; simp only [Ty.idxMentions] at h; simp only [Ty.countI, ih (k + 1) h]
  | mu t ih => intro k h; simp only [Ty.idxMentions] at h; simp [Ty.countI, ih k h, h]
  | tex κ t ih => intro k h; simp only [Ty.idxMentions] at h; simp only [Ty.countI, ih k h]
  | _ => intro k h; simp only [Ty.countI, h]; rfl

theorem countT_zero : ∀ (t : Ty) (k : Nat), t.tyMentions k = false → t.countT k = 0 := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro k h; simp only [Ty.tyMentions, Bool.or_eq_false_iff] at h
      simp only [Ty.countT, iha k h.1, ihb k h.2]
  | refine t ψ ih => intro k h; simp only [Ty.tyMentions] at h; simp only [Ty.countT, ih k h]
  | iall t ih => intro k h; simp only [Ty.tyMentions] at h; simp only [Ty.countT, ih k h]
  | iex t ih => intro k h; simp only [Ty.tyMentions] at h; simp only [Ty.countT, ih k h]
  | tex κ t ih => intro k h; simp only [Ty.tyMentions] at h; simp only [Ty.countT, ih (k + 1) h]
  | mu t ih => intro k h; simp only [Ty.tyMentions] at h; simp [Ty.countT, ih (k + 1) h, h]
  | _ => intro k h; simp only [Ty.countT, h]; rfl

namespace CoupledCl
open CoreLang TermClose

/-! ### info is unchanged by closing, where it is known -/

theorem info_cl (ρ : Nat → Nat) (W : Nat → Ty) : ∀ (t : Ty) (c d : Nat),
    ((info Ty.top t).width.isSome → (info Ty.top (cl ρ W c d t)).width = (info Ty.top t).width) ∧
    ((info Ty.top t).arms.maxW.isSome → (info Ty.top (cl ρ W c d t)).arms = (info Ty.top t).arms) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c d
      have ha := iha c d; have hb := ihb c d
      simp only [cl, info, Info.leaf]
      cases hwa : (info Ty.top a).width with
      | none => simp [Arms.leaf]
      | some wa =>
          cases hwb : (info Ty.top b).width with
          | none => simp [Arms.leaf]
          | some wb =>
              rw [ha.1 (by simp [hwa]), hb.1 (by simp [hwb]), hwa, hwb]
              exact ⟨fun _ => rfl, fun _ => rfl⟩
  | sum a b iha ihb =>
      intro c d
      have ha := iha c d; have hb := ihb c d
      cases hma : (info Ty.top a).arms.maxW with
      | none => simp [cl, info, Arms.combine, hma]
      | some x =>
          cases hmb : (info Ty.top b).arms.maxW with
          | none => simp [cl, info, Arms.combine, hma, hmb]
          | some y =>
              have ea := ha.2 (by simp [hma]); have eb := hb.2 (by simp [hmb])
              simp only [cl, info, ea, eb]
              first | exact ⟨fun _ => rfl, fun _ => rfl⟩ | simp
  | mu t ih => intro c d; simp only [cl, info, top_cons]; exact ih (c + 1) d
  | tex κ t ih => intro c d; simp only [cl, info, top_cons]; exact ih (c + 1) d
  | iall t ih =>
      intro c d
      have h := ih c (d + 1)
      simp only [cl, info, top_shiftI]
      cases hw : (info Ty.top t).width with
      | none =>
          refine ⟨by simp [lowerW], fun hm => ?_⟩
          exact h.2 hm
      | some w => rw [h.1 (by simp [hw]), hw]; exact ⟨fun _ => rfl, fun hm => h.2 hm⟩
  | iex t ih =>
      intro c d
      have h := ih c (d + 1)
      simp only [cl, info, top_shiftI]
      cases hw : (info Ty.top t).width with
      | none =>
          refine ⟨by simp [lowerW], fun hm => ?_⟩
          exact h.2 hm
      | some w => rw [h.1 (by simp [hw]), hw]; exact ⟨fun _ => rfl, fun hm => h.2 hm⟩
  | refine t ψ ih => intro c d; simp only [cl, info]; exact ih c d
  | tvar k => intro c d; simp [info, Info.leaf, Arms.leaf, Ty.top]
  | tok r st => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | _ => intro c d; exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem fits_cl (ρ : Nat → Nat) (W : Nat → Ty) (t : Ty) (c d : Nat) (h : t.fitsGranule = true) :
    (cl ρ W c d t).fitsGranule = true := by
  unfold Ty.fitsGranule Ty.width at *
  cases hw : (info Ty.top t).width with
  | none => simp [hw] at h
  | some w => rw [(info_cl ρ W t c d).1 (by simp [hw]), hw]; rw [hw] at h; exact h

/-! ### Mentions under closing -/

theorem addF_mentions (k : Nat) (x y : Idx) : (addF x y).mentions k = (x.mentions k || y.mentions k) := by
  cases x <;> cases y <;> simp [addF, Idx.mentions]

theorem subF_mentions (k : Nat) (x y : Idx) : (subF x y).mentions k = (x.mentions k || y.mentions k) := by
  cases x <;> cases y <;> simp [subF, Idx.mentions]

theorem smulF_mentions (k n : Nat) (x : Idx) : (smulF n x).mentions k = x.mentions k := by
  cases x <;> simp [smulF, Idx.mentions]

theorem clI_mentions (ρ : Nat → Nat) (d k : Nat) : ∀ i : Idx,
    (clI ρ d i).mentions k = true → k < d ∧ i.mentions k = true
  | .lit n => by simp [clI, Idx.mentions]
  | .var j => by
      by_cases h : j < d
      · simp only [clI, h, ↓reduceIte, Idx.mentions, beq_iff_eq]; intro e; subst e; simp [h]
      · simp [clI, h, Idx.mentions]
  | .add i j => by
      have hi := clI_mentions ρ d k i; have hj := clI_mentions ρ d k j
      simp only [clI, addF_mentions, Idx.mentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(hi h).1, Or.inl (hi h).2⟩
      · exact ⟨(hj h).1, Or.inr (hj h).2⟩
  | .sub i j => by
      have hi := clI_mentions ρ d k i; have hj := clI_mentions ρ d k j
      simp only [clI, subF_mentions, Idx.mentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(hi h).1, Or.inl (hi h).2⟩
      · exact ⟨(hj h).1, Or.inr (hj h).2⟩
  | .smul n i => by
      simp only [clI, smulF_mentions, Idx.mentions]; exact clI_mentions ρ d k i

theorem clM_mentions (ρ : Nat → Nat) (d k : Nat) (μ : Mode) :
    (clM ρ d μ).mentions k = true → k < d ∧ μ.mentions k = true := by
  cases μ <;> simp [clM, Mode.mentions]; exact clI_mentions ρ d k _

theorem clP_mentions (ρ : Nat → Nat) (d k : Nat) : ∀ ψ : Pred,
    (clP ρ d ψ).mentions k = true → k < d ∧ ψ.mentions k = true
  | .tt => by simp [clP, Pred.mentions]
  | .le i j => by
      have hi := clI_mentions ρ d k i; have hj := clI_mentions ρ d k j
      simp only [clP, Pred.mentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(hi h).1, Or.inl (hi h).2⟩
      · exact ⟨(hj h).1, Or.inr (hj h).2⟩
  | .eq i j => by
      have hi := clI_mentions ρ d k i; have hj := clI_mentions ρ d k j
      simp only [clP, Pred.mentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(hi h).1, Or.inl (hi h).2⟩
      · exact ⟨(hj h).1, Or.inr (hj h).2⟩
  | .and p q => by
      have hi := clP_mentions ρ d k p; have hj := clP_mentions ρ d k q
      simp only [clP, Pred.mentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(hi h).1, Or.inl (hi h).2⟩
      · exact ⟨(hj h).1, Or.inr (hj h).2⟩
  | .ini i => by simp only [clP, Pred.mentions]; exact clI_mentions ρ d k i

/-- Index mentions of a closure: only bound ones, and only those already there. -/
theorem idxMentions_cl (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).idxMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), (cl ρ W c d t).idxMentions k = true → k < d ∧ t.idxMentions k = true := by
  intro t
  induction t with
  | intS i => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k i
  | word r P => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k r
  | word2 r P => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k r
  | tok2 r P i j =>
      intro c d k
      simp only [cl, Ty.idxMentions, Bool.or_eq_true]
      intro h; rcases h with (h | h) | h
      · exact ⟨(clI_mentions ρ d k r h).1, Or.inl (Or.inl (clI_mentions ρ d k r h).2)⟩
      · exact ⟨(clI_mentions ρ d k i h).1, Or.inl (Or.inr (clI_mentions ρ d k i h).2)⟩
      · exact ⟨(clI_mentions ρ d k j h).1, Or.inr (clI_mentions ρ d k j h).2⟩
  | epair r P => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k r
  | tokE r P i =>
      intro c d k
      simp only [cl, Ty.idxMentions, Bool.or_eq_true]
      intro h; rcases h with h | h
      · exact ⟨(clI_mentions ρ d k r h).1, Or.inl (clI_mentions ρ d k r h).2⟩
      · exact ⟨(clI_mentions ρ d k i h).1, Or.inr (clI_mentions ρ d k i h).2⟩
  | share r => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k r
  | cap s r => intro c d k; simp only [cl, Ty.idxMentions]; exact clI_mentions ρ d k r
  | tok r st =>
      intro c d k
      rcases st with _ | ⟨P, i⟩
      · simp only [cl, Ty.idxMentions, Option.map, Option.any, Bool.or_false]
        exact clI_mentions ρ d k r
      · simp only [cl, Ty.idxMentions, Option.map, Option.any, Bool.or_eq_true]
        intro h; rcases h with h | h
        · exact ⟨(clI_mentions ρ d k r h).1, Or.inl (clI_mentions ρ d k r h).2⟩
        · exact ⟨(clI_mentions ρ d k i h).1, Or.inr (clI_mentions ρ d k i h).2⟩
  | prod a b iha ihb =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | sum a b iha ihb =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | code a b iha ihb =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | array i t ih =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(clI_mentions ρ d k i h).1, Or.inl (clI_mentions ρ d k i h).2⟩
      · exact ⟨(ih c d k h).1, Or.inr (ih c d k h).2⟩
  | ptr μ t ih =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(clM_mentions ρ d k μ h).1, Or.inl (clM_mentions ρ d k μ h).2⟩
      · exact ⟨(ih c d k h).1, Or.inr (ih c d k h).2⟩
  | ptrOpt μ t ih =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(clM_mentions ρ d k μ h).1, Or.inl (clM_mentions ρ d k μ h).2⟩
      · exact ⟨(ih c d k h).1, Or.inr (ih c d k h).2⟩
  | loc μ t ih =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(clM_mentions ρ d k μ h).1, Or.inl (clM_mentions ρ d k μ h).2⟩
      · exact ⟨(ih c d k h).1, Or.inr (ih c d k h).2⟩
  | refine t ψ ih =>
      intro c d k; simp only [cl, Ty.idxMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(ih c d k h).1, Or.inl (ih c d k h).2⟩
      · exact ⟨(clP_mentions ρ d k ψ h).1, Or.inr (clP_mentions ρ d k ψ h).2⟩
  | mu t ih => intro c d k; simp only [cl, Ty.idxMentions]; exact ih (c + 1) d k
  | tex κ t ih => intro c d k; simp only [cl, Ty.idxMentions]; exact ih (c + 1) d k
  | iall t ih =>
      intro c d k; simp only [cl, Ty.idxMentions]; intro h
      have := ih c (d + 1) (k + 1) h; exact ⟨by omega, this.2⟩
  | iex t ih =>
      intro c d k; simp only [cl, Ty.idxMentions]; intro h
      have := ih c (d + 1) (k + 1) h; exact ⟨by omega, this.2⟩
  | tvar j =>
      intro c d k
      by_cases h : j < c
      · simp [cl, h, Ty.idxMentions]
      · simp only [cl, h, ↓reduceIte, hW]; simp
  | _ => intro c d k; simp [cl, Ty.idxMentions]

/-- Type mentions of a closure. -/
theorem tyMentions_cl (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).tyMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), (cl ρ W c d t).tyMentions k = true → k < c ∧ t.tyMentions k = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro c d k; simp only [cl, Ty.tyMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | sum a b iha ihb =>
      intro c d k; simp only [cl, Ty.tyMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | code a b iha ihb =>
      intro c d k; simp only [cl, Ty.tyMentions, Bool.or_eq_true]; intro h
      rcases h with h | h
      · exact ⟨(iha c d k h).1, Or.inl (iha c d k h).2⟩
      · exact ⟨(ihb c d k h).1, Or.inr (ihb c d k h).2⟩
  | array i t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c d k
  | ptr μ t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c d k
  | ptrOpt μ t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c d k
  | loc μ t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c d k
  | refine t ψ ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c d k
  | iall t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c (d + 1) k
  | iex t ih => intro c d k; simp only [cl, Ty.tyMentions]; exact ih c (d + 1) k
  | mu t ih =>
      intro c d k; simp only [cl, Ty.tyMentions]; intro h
      have := ih (c + 1) d (k + 1) h; exact ⟨by omega, this.2⟩
  | tex κ t ih =>
      intro c d k; simp only [cl, Ty.tyMentions]; intro h
      have := ih (c + 1) d (k + 1) h; exact ⟨by omega, this.2⟩
  | tvar j =>
      intro c d k
      by_cases h : j < c
      · simp only [cl, h, ↓reduceIte, Ty.tyMentions, beq_iff_eq]; intro e; subst e; simp [h]
      · simp only [cl, h, ↓reduceIte, hW]; simp
  | _ => intro c d k; simp [cl, Ty.tyMentions]

theorem tb_tyMentions : ∀ (t : Ty) (c k : Nat), tb c t = true → c ≤ k → t.tyMentions k = false := by
  intro t
  induction t with
  | tvar j => intro c k h hk; simp [tb] at h; simp [Ty.tyMentions]; omega
  | prod a b iha ihb => intro c k h hk; simp only [tb, Bool.and_eq_true] at h; simp [Ty.tyMentions, iha c k h.1 hk, ihb c k h.2 hk]
  | sum a b iha ihb => intro c k h hk; simp only [tb, Bool.and_eq_true] at h; simp [Ty.tyMentions, iha c k h.1 hk, ihb c k h.2 hk]
  | code a b iha ihb => intro c k h hk; simp only [tb, Bool.and_eq_true] at h; simp [Ty.tyMentions, iha c k h.1 hk, ihb c k h.2 hk]
  | array i t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | ptr μ t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | ptrOpt μ t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | loc μ t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | refine t ψ ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | iall t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | iex t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih c k h hk]
  | mu t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih (c + 1) (k + 1) h (by omega)]
  | tex κ t ih => intro c k h hk; simp only [tb] at h; simp [Ty.tyMentions, ih (c + 1) (k + 1) h (by omega)]
  | _ => intro c k h hk; rfl

theorem Clo_tyMentions {s : Ty} (h : Clo s) (k : Nat) : s.tyMentions k = false :=
  tb_tyMentions s 0 k h.1 (Nat.zero_le _)

theorem Clo_idxMentions {s : Ty} (h : Clo s) (k : Nat) : s.idxMentions k = false := by
  have e := h.2 (fun _ => 0) (fun _ => .unit) 0 0
  cases m : s.idxMentions k
  · rfl
  · rw [← e] at m
    have := (idxMentions_cl (fun _ => 0) (fun _ => .unit) (fun _ _ => rfl) s 0 0 k m).1
    omega

/-! ### Counts under closing -/

theorem countT_cl (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).tyMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < c → (cl ρ W c d t).countT k ≤ t.countT k := by
  have hm := tyMentions_cl ρ W hW
  have leaf : ∀ (t : Ty) (c d k : Nat), (cl ρ W c d t).countT k = (if (cl ρ W c d t).tyMentions k then 1 else 0) →
      t.countT k = (if t.tyMentions k then 1 else 0) → (cl ρ W c d t).countT k ≤ t.countT k := by
    intro t c d k e1 e2
    rw [e1, e2]
    cases h1 : (cl ρ W c d t).tyMentions k
    · simp
    · simp [(hm t c d k h1).2]
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.countT]; have := iha c d k h; have := ihb c d k h; omega
  | refine t ψ ih => intro c d k h; simp only [cl, Ty.countT]; exact ih c d k h
  | iall t ih => intro c d k h; simp only [cl, Ty.countT]; exact ih c (d + 1) k h
  | iex t ih => intro c d k h; simp only [cl, Ty.countT]; exact ih c (d + 1) k h
  | tex κ t ih => intro c d k h; simp only [cl, Ty.countT]; exact ih (c + 1) d (k + 1) (by omega)
  | mu t ih =>
      intro c d k h
      simp only [cl, Ty.countT]
      have h1 := ih (c + 1) d (k + 1) (by omega)
      have h2 := ih (c + 1) d 0 (by omega)
      cases e : (cl ρ W (c + 1) d t).tyMentions (k + 1)
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [(hm t (c + 1) d (k + 1) e).2, ↓reduceIte]; omega
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp [cl, hj]
      · simp only [cl, hj, ↓reduceIte]; rw [countT_zero _ k (hW _ _)]; omega
  | sum a b _ _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | code a b _ _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | array i t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | ptr μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | ptrOpt μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | loc μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countT] <;> rfl) (by simp only [Ty.countT] <;> rfl)
  | _ => intro c d k h; simp [cl, Ty.countT, Ty.tyMentions]

theorem countI_cl (ρ : Nat → Nat) (W : Nat → Ty) (hWT : ∀ j m, (W j).tyMentions m = false)
    (hWI : ∀ j m, (W j).idxMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < d → (cl ρ W c d t).countI k ≤ t.countI k := by
  have hm := idxMentions_cl ρ W hWI
  have leaf : ∀ (t : Ty) (c d k : Nat), (cl ρ W c d t).countI k = (if (cl ρ W c d t).idxMentions k then 1 else 0) →
      t.countI k = (if t.idxMentions k then 1 else 0) → (cl ρ W c d t).countI k ≤ t.countI k := by
    intro t c d k e1 e2
    rw [e1, e2]
    cases h1 : (cl ρ W c d t).idxMentions k
    · simp
    · simp [(hm t c d k h1).2]
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.countI]; have := iha c d k h; have := ihb c d k h; omega
  | refine t ψ ih =>
      intro c d k h; simp only [cl, Ty.countI]
      have h1 := ih c d k h
      cases e : (clP ρ d ψ).mentions k
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [(clP_mentions ρ d k ψ e).2, ↓reduceIte]; omega
  | iall t ih => intro c d k h; simp only [cl, Ty.countI]; exact ih c (d + 1) (k + 1) (by omega)
  | iex t ih => intro c d k h; simp only [cl, Ty.countI]; exact ih c (d + 1) (k + 1) (by omega)
  | tex κ t ih => intro c d k h; simp only [cl, Ty.countI]; exact ih (c + 1) d k h
  | mu t ih =>
      intro c d k h
      simp only [cl, Ty.countI]
      have h1 := ih (c + 1) d k h
      have h2 := countT_cl ρ W hWT t (c + 1) d 0 (by omega)
      cases e : (cl ρ W (c + 1) d t).idxMentions k
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [(hm t (c + 1) d k e).2, ↓reduceIte]; omega
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp [cl, hj]
      · simp only [cl, hj, ↓reduceIte]; rw [countI_zero _ k (hWI _ _)]; omega
  | intS i => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | word r P => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | tok r st => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | word2 r P => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | tok2 r P i j => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | epair r P => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | tokE r P i => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | share r => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | cap s r => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | sum a b _ _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | code a b _ _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | array i t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | ptr μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | ptrOpt μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | loc μ t _ => intro c d k h; exact leaf _ c d k (by simp only [cl, Ty.countI] <;> rfl) (by simp only [Ty.countI] <;> rfl)
  | _ => intro c d k h; simp [cl, Ty.countI, Ty.idxMentions]

/-! ### coupledOKIn of a type with bound type variables depends only on the bound part -/

theorem coupledOKIn_agree : ∀ (s : Ty) (c : Nat) (ke1 ke2 : KEnv), tb c s = true →
    (∀ k, k < c → ke1[k]? = ke2[k]?) → Ty.coupledOKIn ke1 s = Ty.coupledOKIn ke2 s := by
  intro s
  induction s with
  | tvar j =>
      intro c ke1 ke2 h ha; simp [tb] at h
      simp only [Ty.coupledOKIn, KEnv.ask, ha j h]
  | prod a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.coupledOKIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | sum a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.coupledOKIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | array i t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.coupledOKIn, ih c ke1 ke2 h ha]
  | refine t ψ ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.coupledOKIn, ih c ke1 ke2 h ha]
  | iall t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.coupledOKIn, ih c ke1 ke2 h ha]
  | iex t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.coupledOKIn, ih c ke1 ke2 h ha]
  | mu t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.coupledOKIn]
      refine ih (c + 1) _ _ h ?_
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | tex κ t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.coupledOKIn]
      rw [ih (c + 1) (some κ :: ke1) (some κ :: ke2) h ?_]
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | _ => intro c ke1 ke2 h ha; rfl

theorem coupledOKIn_closed {s : Ty} (h : tb 0 s = true) (ke1 ke2 : KEnv) :
    Ty.coupledOKIn ke1 s = Ty.coupledOKIn ke2 s :=
  coupledOKIn_agree s 0 ke1 ke2 h (fun _ hk => absurd hk (Nat.not_lt_zero _))

/-! ### The theorem -/

theorem coupledOK_cl (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.share) = true → Ty.coupledOKIn [] (W k) = true) :
    ∀ (t : Ty) (keB : KEnv) (d : Nat), Ty.coupledOKIn (keB ++ ke) t = true →
      tb (keB.length + ke.length) t = true →
      Ty.coupledOKIn keB (cl ρ W keB.length d t) = true := by
  have hWT : ∀ j m, (W j).tyMentions m = false := fun j m => Clo_tyMentions (hC j) m
  have hWI : ∀ j m, (W j).idxMentions m = false := fun j m => Clo_idxMentions (hC j) m
  intro t
  induction t with
  | tvar j =>
      intro keB d h ht
      simp only [tb, decide_eq_true_eq] at ht
      by_cases hj : j < keB.length
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.coupledOKIn, KEnv.ask] at h ⊢
        rwa [List.getElem?_append_left hj] at h
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.coupledOKIn] at h
        have h' : ke.ask (j - keB.length) true (·.share) = true := by
          simp only [KEnv.ask] at h ⊢
          rwa [List.getElem?_append_right (by omega)] at h
        rw [coupledOKIn_closed (hC _).1 keB []]
        exact hW _ (by omega) h'
  | prod a b iha ihb =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb, Bool.and_eq_true] at h ht
      simp only [cl, Ty.coupledOKIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.and_self]
  | sum a b iha ihb =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb, Bool.and_eq_true] at h ht
      simp only [cl, Ty.coupledOKIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.and_self]
  | array i t ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb] at h ht
      simp only [cl, Ty.coupledOKIn, ih keB d h ht]
  | refine t ψ ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb] at h ht
      simp only [cl, Ty.coupledOKIn, ih keB d h ht]
  | iall t ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb] at h ht
      simp only [cl, Ty.coupledOKIn, ih keB (d + 1) h ht]
  | iex t ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ht
      simp only [cl, Ty.coupledOKIn, ih keB (d + 1) h.1 ht, Bool.true_and, Bool.or_eq_true,
        decide_eq_true_eq]
      rcases h.2 with h2 | h2
      · left; have := countI_cl ρ W hWT hWI t keB.length (d + 1) 0 (by omega); omega
      · right; have := fits_cl ρ W (.iex t) keB.length d h2; simpa only [cl] using this
  | mu t ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb] at h ht
      have e := ih (none :: keB) d h (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [cl, Ty.coupledOKIn]
      simpa only [List.length_cons] using e
  | tex κ t ih =>
      intro keB d h ht
      simp only [Ty.coupledOKIn, tb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ht
      have e := ih (some κ :: keB) d h.1 (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [List.length_cons] at e
      simp only [cl, Ty.coupledOKIn, e, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
      rcases h.2 with h2 | h2
      · left; have := countT_cl ρ W hWT t (keB.length + 1) d 0 (by omega); omega
      · right; have := fits_cl ρ W (.tex κ t) keB.length d h2; simpa only [cl] using this
  | _ => intro keB d h ht; simp [cl, Ty.coupledOKIn]

theorem coupledOK_cl0 (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.share) = true → Ty.coupledOKIn [] (W k) = true)
    (t : Ty) (h : Ty.coupledOKIn ke t = true) (ht : tb ke.length t = true) :
    Ty.coupledOK (cl ρ W 0 0 t) = true := by
  have := coupledOK_cl ρ W ke hC hW t [] 0 (by simpa using h) (by simpa using ht)
  simpa [Ty.coupledOK] using this

end CoupledCl

/-- **Closing keeps `coupledOK`** at closed, `coupledOK` share witnesses. -/
theorem coupledOK_cl0 (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv) (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.share) = true → Ty.coupledOKIn [] (W k) = true)
    {t : Ty} (h1 : Ty.coupledOKIn ke t = true) (h2 : tb ke.length t = true) :
    Ty.coupledOK (cl ρ W 0 0 t) = true :=
  CoupledCl.coupledOK_cl0 ρ W ke hC hW t h1 h2

/-- (S7) **Closing keeps region-freedom** (ke-aware, as `coupledOK_cl`): a
region-free type whose unguarded type variables are `share` (what `coupledOKIn`
asks of them) stays region-free when they are replaced by region-free `share`
witnesses (`WitR`).  Variables behind a reference are not looked at. -/
theorem rgnFree_clK (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hW : ∀ k, ke.ask k true (·.share) = true → rgnFree (W k) = true) :
    ∀ (t : Ty) (keB : KEnv) (d : Nat), Ty.coupledOKIn (keB ++ ke) t = true → rgnFree t = true →
      rgnFree (cl ρ W keB.length d t) = true := by
  intro t
  induction t with
  | tvar j =>
      intro keB d h _
      by_cases hj : j < keB.length
      · simp [cl, hj, rgnFree]
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.coupledOKIn] at h
        apply hW
        simp only [KEnv.ask] at h ⊢
        rwa [List.getElem?_append_right (by omega)] at h
  | ptr μ t _ => intro keB d _ h; cases μ <;> simp_all [rgnFree, cl, clM]
  | ptrOpt μ t _ => intro keB d _ h; cases μ <;> simp_all [rgnFree, cl, clM]
  | loc μ t _ => intro keB d _ h; cases μ <;> simp_all [rgnFree, cl, clM]
  | prod a b iha ihb =>
      intro keB d h hr
      simp only [Ty.coupledOKIn, rgnFree, Bool.and_eq_true] at h hr
      simp only [cl, rgnFree, iha keB d h.1 hr.1, ihb keB d h.2 hr.2, Bool.and_self]
  | sum a b iha ihb =>
      intro keB d h hr
      simp only [Ty.coupledOKIn, rgnFree, Bool.and_eq_true] at h hr
      simp only [cl, rgnFree, iha keB d h.1 hr.1, ihb keB d h.2 hr.2, Bool.and_self]
  | array i t ih =>
      intro keB d h hr; simp only [Ty.coupledOKIn, rgnFree] at h hr; simp only [cl, rgnFree]; exact ih keB d h hr
  | refine t ψ ih =>
      intro keB d h hr; simp only [Ty.coupledOKIn, rgnFree] at h hr; simp only [cl, rgnFree]; exact ih keB d h hr
  | iall t ih =>
      intro keB d h hr; simp only [Ty.coupledOKIn, rgnFree] at h hr; simp only [cl, rgnFree]; exact ih keB (d + 1) h hr
  | iex t ih =>
      intro keB d h hr
      simp only [Ty.coupledOKIn, rgnFree, Bool.and_eq_true] at h hr
      simp only [cl, rgnFree]; exact ih keB (d + 1) h.1 hr
  | mu t ih =>
      intro keB d h hr
      simp only [Ty.coupledOKIn, rgnFree] at h hr
      have e := ih (none :: keB) d h hr
      simp only [List.length_cons] at e
      simp only [cl, rgnFree]; exact e
  | tex κ t ih =>
      intro keB d h hr
      simp only [Ty.coupledOKIn, rgnFree, Bool.and_eq_true] at h hr
      have e := ih (some κ :: keB) d h.1 hr
      simp only [List.length_cons] at e
      simp only [cl, rgnFree]; exact e
  | _ => intro keB d _ _; simp [cl, rgnFree]

theorem rgnFree_cl0 (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hW : ∀ k, ke.ask k true (·.share) = true → rgnFree (W k) = true)
    {t : Ty} (h1 : Ty.coupledOKIn ke t = true) (h2 : rgnFree t = true) :
    rgnFree (cl ρ W 0 0 t) = true :=
  rgnFree_clK ρ W ke hW t [] 0 (by simpa using h1) h2

namespace AffineCl

theorem affineIn_agree : ∀ (s : Ty) (c : Nat) (ke1 ke2 : KEnv), tb c s = true →
    (∀ k, k < c → ke1[k]? = ke2[k]?) → Ty.affineIn ke1 s = Ty.affineIn ke2 s := by
  intro s
  induction s with
  | tvar j =>
      intro c ke1 ke2 h ha; simp [tb] at h
      simp only [Ty.affineIn, KEnv.ask, ha j h]
  | prod a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.affineIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | sum a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.affineIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | array i t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.affineIn, ih c ke1 ke2 h ha]
  | refine t ψ ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.affineIn, ih c ke1 ke2 h ha]
  | iall t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.affineIn, ih c ke1 ke2 h ha]
  | iex t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.affineIn, ih c ke1 ke2 h ha]
  | mu t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.affineIn]
      rw [ih (c + 1) (none :: ke1) (none :: ke2) h ?_]
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | tex κ t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.affineIn]
      rw [ih (c + 1) (some κ :: ke1) (some κ :: ke2) h ?_]
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | ptr m t ih => intro c ke1 ke2 h ha; cases m <;> rfl
  | ptrOpt m t ih => intro c ke1 ke2 h ha; cases m <;> rfl
  | loc m t ih => intro c ke1 ke2 h ha; cases m <;> rfl
  | _ => intro c ke1 ke2 h ha; rfl

theorem affineIn_closed {s : Ty} (h : tb 0 s = true) (ke1 ke2 : KEnv) :
    Ty.affineIn ke1 s = Ty.affineIn ke2 s :=
  affineIn_agree s 0 ke1 ke2 h (fun _ hk => absurd hk (Nat.not_lt_zero _))

theorem affine_cl (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.copy) = true → Ty.affine (W k) = false) :
    ∀ (t : Ty) (keB : KEnv) (d : Nat), Ty.affineIn (keB ++ ke) t = false →
      tb (keB.length + ke.length) t = true →
      Ty.affineIn keB (cl ρ W keB.length d t) = false := by
  intro t
  induction t with
  | tvar j =>
      intro keB d h ht
      simp only [tb, decide_eq_true_eq] at ht
      by_cases hj : j < keB.length
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.affineIn, KEnv.ask] at h ⊢
        rwa [List.getElem?_append_left hj] at h
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.affineIn, Bool.not_eq_false'] at h
        have h' : ke.ask (j - keB.length) true (·.copy) = true := by
          simp only [KEnv.ask] at h ⊢
          rwa [List.getElem?_append_right (by omega)] at h
        rw [affineIn_closed (hC _).1 keB []]
        exact hW _ (by omega) h'
  | prod a b iha ihb =>
      intro keB d h ht
      simp only [Ty.affineIn, tb, Bool.and_eq_true, Bool.or_eq_false_iff] at h ht
      simp only [cl, Ty.affineIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.or_self]
  | sum a b iha ihb =>
      intro keB d h ht
      simp only [Ty.affineIn, tb, Bool.and_eq_true, Bool.or_eq_false_iff] at h ht
      simp only [cl, Ty.affineIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.or_self]
  | array i t ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      simp only [cl, Ty.affineIn, ih keB d h ht]
  | refine t ψ ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      simp only [cl, Ty.affineIn, ih keB d h ht]
  | iall t ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      simp only [cl, Ty.affineIn, ih keB (d + 1) h ht]
  | iex t ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      simp only [cl, Ty.affineIn, ih keB (d + 1) h ht]
  | mu t ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      have e := ih (none :: keB) d h (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [cl, Ty.affineIn]
      simpa only [List.length_cons] using e
  | tex κ t ih =>
      intro keB d h ht
      simp only [Ty.affineIn, tb] at h ht
      have e := ih (some κ :: keB) d h (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [cl, Ty.affineIn]
      simpa only [List.length_cons] using e
  | ptr m t ih => intro keB d h ht; cases m <;> simp_all [cl, clM, Ty.affineIn]
  | ptrOpt m t ih => intro keB d h ht; cases m <;> simp_all [cl, clM, Ty.affineIn]
  | loc m t ih => intro keB d h ht; cases m <;> simp_all [cl, clM, Ty.affineIn]
  | _ => intro keB d h ht; simp_all [cl, Ty.affineIn]

theorem affine_cl0 (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.copy) = true → Ty.affine (W k) = false)
    (t : Ty) (h : Ty.affineIn ke t = false) (ht : tb ke.length t = true) :
    Ty.affine (cl ρ W 0 0 t) = false := by
  have := affine_cl ρ W ke hC hW t [] 0 (by simpa using h) (by simpa using ht)
  simpa [Ty.affine] using this

end AffineCl

namespace NoOwnCl

/-- (B.3) `noOwnIn` of a type with bound type variables depends only on the
bound part of the kind environment. -/
theorem noOwnIn_agree : ∀ (s : Ty) (c : Nat) (ke1 ke2 : KEnv), tb c s = true →
    (∀ k, k < c → ke1[k]? = ke2[k]?) → Ty.noOwnIn ke1 s = Ty.noOwnIn ke2 s := by
  intro s
  induction s with
  | tvar j =>
      intro c ke1 ke2 h ha; simp [tb] at h
      simp only [Ty.noOwnIn, KEnv.ask, ha j h]
  | prod a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.noOwnIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | sum a b iha ihb => intro c ke1 ke2 h ha; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.noOwnIn, iha c ke1 ke2 h.1 ha, ihb c ke1 ke2 h.2 ha]
  | array i t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.noOwnIn, ih c ke1 ke2 h ha]
  | refine t ψ ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.noOwnIn, ih c ke1 ke2 h ha]
  | iall t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.noOwnIn, ih c ke1 ke2 h ha]
  | iex t ih => intro c ke1 ke2 h ha; simp only [tb] at h; simp only [Ty.noOwnIn, ih c ke1 ke2 h ha]
  | mu t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.noOwnIn]
      refine ih (c + 1) _ _ h ?_
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | tex κ t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      simp only [Ty.noOwnIn]
      rw [ih (c + 1) (some κ :: ke1) (some κ :: ke2) h ?_]
      intro k hk; cases k with
      | zero => rfl
      | succ k => simp only [List.getElem?_cons_succ]; exact ha k (by omega)
  | ptr m t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      cases m with
      | own => rfl
      | pub => simp only [Ty.noOwnIn]; exact ih c ke1 ke2 h ha
      | rgn _ => rfl
  | ptrOpt m t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      cases m with
      | own => rfl
      | pub => simp only [Ty.noOwnIn]; exact ih c ke1 ke2 h ha
      | rgn _ => rfl
  | loc m t ih =>
      intro c ke1 ke2 h ha; simp only [tb] at h
      cases m with
      | own => rfl
      | pub => simp only [Ty.noOwnIn]; exact ih c ke1 ke2 h ha
      | rgn _ => rfl
  | _ => intro c ke1 ke2 h ha; rfl

theorem noOwnIn_closed {s : Ty} (h : tb 0 s = true) (ke1 ke2 : KEnv) :
    Ty.noOwnIn ke1 s = Ty.noOwnIn ke2 s :=
  noOwnIn_agree s 0 ke1 ke2 h (fun _ hk => absurd hk (Nat.not_lt_zero _))

theorem noOwn_cl (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.noOwn) = true → Ty.noOwnIn [] (W k) = true) :
    ∀ (t : Ty) (keB : KEnv) (d : Nat), Ty.noOwnIn (keB ++ ke) t = true →
      tb (keB.length + ke.length) t = true →
      Ty.noOwnIn keB (cl ρ W keB.length d t) = true := by
  intro t
  induction t with
  | tvar j =>
      intro keB d h ht
      simp only [tb, decide_eq_true_eq] at ht
      by_cases hj : j < keB.length
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.noOwnIn, KEnv.ask] at h ⊢
        rwa [List.getElem?_append_left hj] at h
      · simp only [cl, hj, ↓reduceIte]
        simp only [Ty.noOwnIn] at h
        have h' : ke.ask (j - keB.length) true (·.noOwn) = true := by
          simp only [KEnv.ask] at h ⊢
          rwa [List.getElem?_append_right (by omega)] at h
        rw [noOwnIn_closed (hC _).1 keB []]
        exact hW _ (by omega) h'
  | prod a b iha ihb =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb, Bool.and_eq_true] at h ht
      simp only [cl, Ty.noOwnIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.and_self]
  | sum a b iha ihb =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb, Bool.and_eq_true] at h ht
      simp only [cl, Ty.noOwnIn, iha keB d h.1 ht.1, ihb keB d h.2 ht.2, Bool.and_self]
  | array i t ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb] at h ht
      simp only [cl, Ty.noOwnIn, ih keB d h ht]
  | refine t ψ ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb] at h ht
      simp only [cl, Ty.noOwnIn, ih keB d h ht]
  | iall t ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb] at h ht
      simp only [cl, Ty.noOwnIn, ih keB (d + 1) h ht]
  | iex t ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb] at h ht
      simp only [cl, Ty.noOwnIn, ih keB (d + 1) h ht]
  | mu t ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb] at h ht
      have e := ih (none :: keB) d h (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [cl, Ty.noOwnIn]
      simpa only [List.length_cons] using e
  | tex κ t ih =>
      intro keB d h ht
      simp only [Ty.noOwnIn, tb, Bool.and_eq_true] at h ht
      have e := ih (some κ :: keB) d h.2 (by simp only [List.length_cons]; rw [show keB.length + 1 + ke.length = keB.length + ke.length + 1 by omega]; exact ht)
      simp only [List.length_cons] at e
      simp only [cl, Ty.noOwnIn, h.1, e, Bool.and_self]
  | ptr m t ih =>
      intro keB d h ht
      simp only [tb] at ht
      cases m with
      | own => simp [Ty.noOwnIn] at h
      | pub => simp only [Ty.noOwnIn] at h; simp only [cl, clM, Ty.noOwnIn]; exact ih keB d h ht
      | rgn _ => simp [cl, clM, Ty.noOwnIn]
  | ptrOpt m t ih =>
      intro keB d h ht
      simp only [tb] at ht
      cases m with
      | own => simp [Ty.noOwnIn] at h
      | pub => simp only [Ty.noOwnIn] at h; simp only [cl, clM, Ty.noOwnIn]; exact ih keB d h ht
      | rgn _ => simp [cl, clM, Ty.noOwnIn]
  | loc m t ih =>
      intro keB d h ht
      simp only [tb] at ht
      cases m with
      | own => simp [Ty.noOwnIn] at h
      | pub => simp only [Ty.noOwnIn] at h; simp only [cl, clM, Ty.noOwnIn]; exact ih keB d h ht
      | rgn _ => simp [cl, clM, Ty.noOwnIn]
  | _ => intro keB d h ht; simp [cl, Ty.noOwnIn]

/-- (B.3) **Closing keeps `noOwn`** at closed, `noOwn` witnesses of `noOwn`
variables. -/
theorem noOwn_cl0 (ρ : Nat → Nat) (W : Nat → Ty) (ke : KEnv)
    (hC : ∀ k, Clo (W k))
    (hW : ∀ k, k < ke.length → ke.ask k true (·.noOwn) = true → Ty.noOwnIn [] (W k) = true)
    (t : Ty) (h : Ty.noOwnIn ke t = true) (ht : tb ke.length t = true) :
    Ty.noOwn (cl ρ W 0 0 t) = true := by
  have := noOwn_cl ρ W ke hC hW t [] 0 (by simpa using h) (by simpa using ht)
  simpa [Ty.noOwn] using this

end NoOwnCl

theorem admitsIn_share {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) (hs : κ.share = true) :
    Ty.coupledOKIn cx.ke σ = true := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hsh⟩, _⟩, _⟩, _⟩, _⟩ := h
  simpa [hs] using hsh

theorem admitsIn_arrFree {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) : σ.arrFree = true := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, ha⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact ha

theorem admitsIn_word {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) :
    (κ.noWord = true → Ty.wordFreeIn cx.ke σ = true) ∧ (κ.copy = true → Ty.affineIn cx.ke σ = false) := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hc⟩, hw⟩, _⟩ := h
  exact ⟨fun e => by simpa [e] using hw, fun e => by simpa [e] using hc⟩

theorem admitsIn_noOwn {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) (hn : κ.noOwn = true) :
    Ty.noOwnIn cx.ke σ = true := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hno⟩, _⟩, _⟩, _⟩ := h
  simpa [hn] using hno

theorem admitsIn_wf {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) :
    σ.wf cx.ke.length cx.inames.length = true := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact hw

theorem WitAF_CE (η : TEnv) : WitAF (CE η) := fun _ => ⟨rfl, rfl, rfl⟩

/-- The frame invariant; T3c-4b adds layout agreement (`WitL`) and that the
frame's type variables are its runtime type arguments' (`ke` vs `σs`); the
arguments respect the kinds' word exclusion (`KindsOK`); T3c-5a, witnesses hold
no by-value array (`WitAF`). -/
def FInv (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (K : TEnv → List Word → Prop) (cx : Cx) (env : Env) : Prop :=
  Sat cx.facts ρ ∧ VarsOK ρ η σs cx.vars env ∧ RetOK ρ η σs cx.ret K ∧ WitL σs η.wit cx.opq ∧
    cx.ke.length ≤ σs.length ∧ KindsOK cx.ke σs ∧ WitAF η ∧ WitSh cx.ke η ∧ WitC cx.ke η ∧ WitN cx.ke η ∧
    WitR cx.ke η

/-- A frame's type environment is about the running program and coherent. -/
def EnvOK (p : Prog) (η : TEnv) : Prop := η.prog = p ∧ Coh η ∧ CohR η

theorem VarsOK_ext {η η' : TEnv} (hc : Coh η) (he : Ext η η') {ρ : Nat → Nat} {σs : List Ty}
    {vars : List (String × Ty × Bool)} {env : Env} (h : VarsOK ρ η σs vars env) : VarsOK ρ η' σs vars env := by
  intro x e hx
  obtain ⟨rt, ws, hl, hv, hs⟩ := h x e hx
  exact ⟨rt, ws, hl, VR_ext hc he hv, hs⟩

/-- **A frame survives Σ's growth.** -/
theorem FInv_ext {η η' : TEnv} (hc : Coh η) (he : Ext η η') {ρ : Nat → Nat} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx : Cx} {env : Env} (hi : FInv ρ η σs K cx env) :
    FInv ρ η' σs K cx env :=
  ⟨hi.1, VarsOK_ext hc he hi.2.1, fun η'' h2 => hi.2.2.1 η'' (Ext_trans he h2),
    by rw [he.2.1]; exact hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1,
    ⟨fun k => by rw [he.2.1]; exact hi.2.2.2.2.2.2.1 k, fun k hk => by rw [he.2.1]; exact hi.2.2.2.2.2.2.2.1 k hk,
      fun k hk => by rw [he.2.1]; exact hi.2.2.2.2.2.2.2.2.1 k hk,
      fun k hk => by rw [he.2.1]; exact hi.2.2.2.2.2.2.2.2.2.1 k hk,
      fun k hk => by rw [he.2.1]; exact hi.2.2.2.2.2.2.2.2.2.2 k hk⟩⟩

/-! ### P3 (b): the resourceful frame invariant -/

theorem secondClass_shiftI (c : Nat) (t : Ty) : (t.shiftI c).secondClass = t.secondClass := by
  induction t generalizing c <;> simp_all [Ty.shiftI, Ty.secondClass]

theorem secondClass_shiftT (c : Nat) (t : Ty) : (t.shiftT c).secondClass = t.secondClass := by
  induction t generalizing c <;> simp_all [Ty.shiftT, Ty.secondClass] <;> split <;> rfl

/-- Does the frame still hold variable `e`'s resources?  Live (not yet used),
or lent to a borrow (counted until `endBorrow`). -/
def Holds (cx : Cx) (e : String × Ty × Bool) : Bool := e.2.2 || decide (e.1 ∈ cx.lent)

/-- (P3) The frame's holdings are at most `Rf`: each held variable's value
carries `Rx x` (exactly, `VRR`), and they sum to at most `Rf`.  Names are
unique (`Cx.bind` refuses shadowing), so each is counted once; every lent name
is a variable already marked used (`borrow` uses it first), so a lent value is
counted through `lent` only, and is not second-class (a token or a share), so
`endBorrow`'s sweep of second-class variables keeps it.  The slack absorbs
drops (D1). -/
def HeldOK (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (env : Env) (Rf : Res) : Prop :=
  (cx.vars.map (·.1)).Nodup ∧ cx.lent.Nodup ∧
  (∀ y ∈ cx.lent, ∃ e ∈ cx.vars, e.1 = y ∧ e.2.2 = false ∧ e.2.1.secondClass = false) ∧
  ∃ Rx : String → Res,
    (∀ x e, cx.vars.find? (·.1 == x) = some e → Holds cx e = true →
      ∃ rt ws, lookupE env x = some (rt, ws) ∧ VRR ρ η e.2.1 (shp rt) ws (Rx x)) ∧
    Res.sum ((cx.vars.filter (Holds cx)).map (fun e => Rx e.1)) ≤ Rf

/-- (P3, D4) `RetOK` with resources: the continuation is told the returned
value's resources and the frame's region counter at return. -/
def RetOKR (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (ret : Ty)
    (K : TEnv → Nat → List Word → Res → Prop) : Prop :=
  ∀ η', Ext η η' → ∀ ws R, VRR ρ η' ret (shp (close σs ret)) ws R → Lay σs ret (close σs ret) ws →
    K (CE η') η'.rid ws R

end TermSound

/-! ## Pub-position words (`cnt`) (moved unchanged from `TermPtrRtsDefs`: `ThInvRE`/`ResumeR` read them) -/

namespace TermPtrRts
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound

/-- `pub` (not `own`, not a region's). -/
def mPub : Mode → Bool
  | .pub => true
  | _ => false

/-- **Shallow pub-ness**: every reference at a value position is `pub` and every package kind
there is `noOwn` (positions under a reference, and type variables, are not looked at).  Array
elements are looked at. -/
def sNo : Ty → Bool
  | .ptr μ _ => mPub μ
  | .ptrOpt μ _ => mPub μ
  | .loc μ _ => mPub μ
  | .prod a b => sNo a && sNo b
  | .sum a b => sNo a && sNo b
  | .refine t _ => sNo t
  | .iall t => sNo t
  | .iex t => sNo t
  | .mu t => sNo t
  | .tex κ t => κ.noOwn && sNo t
  | .array _ t => sNo t
  | _ => true

mutual
/-- The words of a value of runtime type `rt` that are counted (`cnt`): all of them under a
shallow-pub (`sNo`) type; otherwise structurally — a `pub` reference's words, the two halves of a
pair, a non-boxed sum's decoded arm payload (decoded at the `lnorm` arms, so skeleton- and
token-erasure-invariant), a boxed sum's box reference, the body under a binder or refinement (an
array is never a value: only under `sNo`); nothing at an `own`/region reference or a type variable. -/
def pubWords : Ty → List Word → List Word
  | .prod a b, ws =>
      if sNo (.prod a b) then ws else
      match wc a with
      | some n => pubWords a (ws.take n) ++ pubWords b (ws.drop n)
      | none => []
  | .sum a b, ws =>
      if sNo (.sum a b) then ws else
      if (Ty.sum a b).tier = .boxed then ws
      else
        match decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
        | some (j, p) => if j < (armsOf a).length then pubArm a j p else pubArm b (j - (armsOf a).length) p
        | none => []
  | .refine t ψ, ws => if sNo (.refine t ψ) then ws else pubWords t ws
  | .iall t, ws => if sNo (.iall t) then ws else pubWords t ws
  | .iex t, ws => if sNo (.iex t) then ws else pubWords t ws
  | .mu t, ws => if sNo (.mu t) then ws else pubWords t ws
  | .tex κ t, ws => if sNo (.tex κ t) then ws else pubWords t ws
  -- (D1) `array` falls here: an array is never a value (`accs` is `none`), so cnt on
  -- arrFree types is unchanged by dropping the per-element case.
  | t, ws => if sNo t then ws else []

/-- `pubWords` of the payload `p` of arm `j` of a (possibly nested) sum. -/
def pubArm : Ty → Nat → List Word → List Word
  | .sum a b, j, p => if j < (armsOf a).length then pubArm a j p else pubArm b (j - (armsOf a).length) p
  | .refine t _, j, p => pubArm t j p
  | .iall t, j, p => pubArm t j p
  | .iex t, j, p => pubArm t j p
  | .mu t, j, p => pubArm t j p
  | .tex _ t, j, p => pubArm t j p
  | t, _, p => pubWords t p
end

end TermPtrRts

namespace TermSound
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv

/-- The stack below a frame, as a return continuation: returning `ws` into the
top frame `f` resumes a well-typed caller, whose own continuation is the rest.
(T3c-4) The caller's context keeps its types in scope (`TvOK`, TermTv).  (RetPw) Each frame
carries the return link of the frame below it, as in `ResumeR`. -/
def Resume (p : Prog) : List Frame → TEnv → List Word → Prop
  | [], _, _ => True
  | f :: rest, E, ws => ∃ ρ η c, CE η = E ∧ EnvOK p η ∧ Typed p c f.body ∧ TvOK c ∧
      FInv ρ η f.σs (Resume p rest) c ((f.x, f.ty, ws) :: f.env) ∧
      ∀ (f' : Frame) (rest' : List Frame), rest = f' :: rest' → ∀ ws,
        TermPtrRts.pubWords f'.ty ws = TermPtrRts.pubWords (close f.σs c.ret) ws

/-- (P3, D6) The resourceful frame invariant, by bridge: the old `FInv` at a
trivial continuation, plus the resourceful return clause and the holdings. -/
def FInvR (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (K : TEnv → Nat → List Word → Res → Prop)
    (cx : Cx) (env : Env) (Rf : Res) : Prop :=
  FInv ρ η σs (fun _ _ => True) cx env ∧ RetOKR ρ η σs cx.ret K ∧ HeldOK ρ η cx env Rf

/-- (A1 checker invariant) A frame's typing: `Typed`, at the checker's context (`CkW`: `checkW` accepts the
rest of the block, the variables are `wrapOK`, the non-opaque witnesses `argTop`). -/
def TypedK (p : Prog) (η : TEnv) (cx : Cx) (e : Expr) : Prop := Typed p cx e ∧ TermA4.CkW p η.wit cx e

/-- `TypedK` reads the view only through its witnesses. -/
theorem TypedK.wit {p : Prog} {η η' : TEnv} {cx : Cx} {e : Expr} (h : TypedK p η cx e)
    (hw : η'.wit = η.wit) : TypedK p η' cx e :=
  ⟨h.1, by unfold TypedK at h; rw [hw]; exact h.2⟩

/-- `TypedK` along `Ext` (Σ's growth keeps the witnesses). -/
theorem TypedK.ext {p : Prog} {η η' : TEnv} {cx : Cx} {e : Expr} (h : TypedK p η cx e)
    (hx : Ext η η') : TypedK p η' cx e :=
  h.wit hx.2.1

/-- (P3, D4) The stack below a frame, holding `Rs`, as a resourceful return
continuation: returning `ws` carrying `R` at thread view `E` and counter `rd`
resumes the caller holding its own `Rc` plus `R`; the rest holds `Rrest`. -/
def ResumeR (p : Prog) : List Frame → Res → TEnv → Nat → List Word → Res → Prop
  | [], Rs, _, _, _, _ => Rs = .zero
  | f :: rest, Rs, E, rd, ws, R => ∃ Rc Rrest, Rs = Rc + Rrest ∧ ∃ ρ η c, CE η = E ∧ η.rid = rd ∧
      EnvOK p η ∧ TypedK p η c f.body ∧ TvOK c ∧
      FInvR ρ η f.σs (ResumeR p rest Rrest) c ((f.x, f.ty, ws) :: f.env) (Rc + R) ∧
      ∀ (f' : Frame) (rest' : List Frame), rest = f' :: rest' → ∀ ws,
        TermPtrRts.pubWords f'.ty ws = TermPtrRts.pubWords (close f.σs c.ret) ws

/-- (P3, D4/D5) A thread holding at most `Tot`: its frame's `Rf` plus its
stack's `Rs`. -/
def ThInvR (p : Prog) (th : TTh) (Tot : Res) : Prop :=
  ∃ ρ η cx Rf Rs, EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
    FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot

/-- `ThInvR` with the thread-wide part of the frame's view named. -/
def ThInvRE (p : Prog) (E : TEnv) (th : TTh) (Tot : Res) : Prop :=
  ∃ ρ η cx Rf Rs, CE η = E ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
    FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot ∧
    ∀ (f : Frame) (rest : List Frame), th.stack = f :: rest → ∀ ws,
      TermPtrRts.pubWords f.ty ws = TermPtrRts.pubWords (close th.σs cx.ret) ws

/-- (RetPw) The top frame's return link (`ThInvRE`'s last conjunct is `RetPw th.σs th.stack cx.ret`). -/
def RetPw (σs : List Ty) (stack : List Frame) (ret : Ty) : Prop :=
  ∀ (f : Frame) (rest : List Frame), stack = f :: rest → ∀ ws,
    TermPtrRts.pubWords f.ty ws = TermPtrRts.pubWords (close σs ret) ws

/-- (RetPw) Counted words read only the skeleton (supplied by `TermK2a.pubWords_of_skel`). -/
def PwSkel : Prop :=
  ∀ (t u : Ty), skel t = skel u → ∀ ws : List Word, TermPtrRts.pubWords t ws = TermPtrRts.pubWords u ws

/-- (RetPw) Subsumption keeps the counted words (supplied by `TermK2a.pubWords_subS`). -/
def PwSubS : Prop :=
  ∀ (cx : Cx) (σ τ : Ty), SubS cx σ τ → ∀ (σs : List Ty) (c d : Nat) (ws : List Word),
    TermPtrRts.pubWords (substTs σs c d σ) ws = TermPtrRts.pubWords (substTs σs c d τ) ws

/-- (RetPw) Counted words read only the signature (supplied by `TermK2a.pubWords_sig`). -/
def PwSig : Prop := ∀ (t : Ty) (ws : List Word), TermPtrRts.pubWords (sig t) ws = TermPtrRts.pubWords t ws

/-- (RetPw) The link moves along a skeleton-preserving change of the closed return type. -/
theorem retPw_skel {σs σs2 : List Ty} {st : List Frame} {r r2 : Ty} (hS : PwSkel) (h : RetPw σs st r)
    (hk : skel (close σs2 r2) = skel (close σs r)) : RetPw σs2 st r2 :=
  fun f rest hst ws => (h f rest hst ws).trans (hS _ _ hk.symm ws)

/-- (RetPw) Transport the return link along an equality of return types. -/
theorem retPw_eq {σs : List Ty} {st : List Frame} {r r2 : Ty} (h : RetPw σs st r) (e : r2 = r) :
    RetPw σs st r2 := by
  subst e; exact h

theorem ThInvRE.thInvR {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} (h : ThInvRE p E th Tot) :
    ThInvR p th Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, -, hE, hT, hv, hF, hs, -⟩ := h
  exact ⟨ρ, η, cx, Rf, Rs, hE, hT, hv, hF, hs⟩

/-! Basic facts. -/

theorem HeldOK_mono {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf Rf' : Res}
    (h : HeldOK ρ η cx env Rf) (hle : Rf ≤ Rf') : HeldOK ρ η cx env Rf' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.elim fun Rx hx => ⟨Rx, hx.1, Res.le_trans hx.2 hle⟩⟩

theorem HeldOK_ext {η η' : TEnv} (hc : Coh η) (hr : CohR η) (he : Ext η η') {ρ : Nat → Nat}
    {cx : Cx} {env : Env} {Rf : Res} (h : HeldOK ρ η cx env Rf) : HeldOK ρ η' cx env Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := h
  refine ⟨hn, hln, hlent, Rx, fun x e hf hh => ?_, hs⟩
  obtain ⟨rt, ws, hl, hv⟩ := hx x e hf hh
  exact ⟨rt, ws, hl, VRR_ext hc hr he hv⟩

theorem RetOKR_ext {η η' : TEnv} (he : Ext η η') {ρ : Nat → Nat} {σs : List Ty} {ret : Ty}
    {K : TEnv → Nat → List Word → Res → Prop} (h : RetOKR ρ η σs ret K) : RetOKR ρ η' σs ret K :=
  fun η'' h2 => h η'' (Ext_trans he h2)

/-- **A resourceful frame survives Σ's growth.** -/
theorem FInvR_ext {η η' : TEnv} (hc : Coh η) (hr : CohR η) (he : Ext η η') {ρ : Nat → Nat}
    {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop} {cx : Cx} {env : Env} {Rf : Res}
    (h : FInvR ρ η σs K cx env Rf) : FInvR ρ η' σs K cx env Rf :=
  ⟨FInv_ext hc he h.1, RetOKR_ext he h.2.1, HeldOK_ext hc hr he h.2.2⟩

theorem FInvR_mono {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {Rf Rf' : Res} (h : FInvR ρ η σs K cx env Rf) (hle : Rf ≤ Rf') :
    FInvR ρ η σs K cx env Rf' :=
  ⟨h.1, h.2.1, HeldOK_mono h.2.2 hle⟩

/-- A thread's bound may be raised: the slack goes to the frame. -/
theorem ThInvR_mono {p : Prog} {th : TTh} {Tot Tot' : Res} (h : ThInvR p th Tot) (hle : Tot ≤ Tot') :
    ThInvR p th Tot' := by
  obtain ⟨ρ, η, cx, Rf, Rs, hE, hT, htv, hi, hs⟩ := h
  obtain ⟨d, hd⟩ : ∃ d : Res, ∀ k, d k = Tot' k - Tot k := ⟨fun k => Tot' k - Tot k, fun _ => rfl⟩
  refine ⟨ρ, η, cx, Rf + d, Rs, hE, hT, htv, FInvR_mono hi (Res.le_add_right _ _), ?_⟩
  subst hs
  refine Res.ext fun k => ?_
  have := hle k
  have := hd k
  simp only [Res.add_apply] at *
  omega



theorem peek_VR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) :
    ∃ rt ws, evalAt env a = some (rt, ws) ∧ VR ρ η t (shp rt) ws ∧ Lay σs t rt ws := by
  cases a with
  | lit n =>
      simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h
      refine ⟨_, _, rfl, by simp [VR, ev], ?_, rfl, by simp [wc, accs], trivial, rfl⟩
      intro us hu; simp [accs] at hu; subst hu; rfl
  | unit =>
      simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at h; subst h
      refine ⟨_, _, rfl, by simp [VR], ?_, rfl, by simp [wc, accs], trivial, rfl⟩
      intro us hu; simp [accs] at hu; subst hu; rfl
  | var x =>
      simp only [Cx.peek, Cx.find, bind_ok_iff] at h
      obtain ⟨⟨t', b⟩, hf, h⟩ := h
      split at hf
      · rename_i y u b' hy
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        split at h
        · simp at h
        · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          exact hv x _ hy
      · simp at hf

theorem find_map_flags (vars : List (String × Ty × Bool)) (f : String × Ty × Bool → String × Ty × Bool)
    (hf : ∀ e, (f e).1 = e.1) (x : String) :
    (vars.map f).find? (·.1 == x) = (vars.find? (·.1 == x)).map f := by
  induction vars with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, List.find?_cons, hf e]
      split <;> simp_all

theorem VarsOK_flags {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {vars : List (String × Ty × Bool)} {env : Env}
    (f : String × Ty × Bool → String × Ty × Bool) (hf : ∀ e, (f e).1 = e.1 ∧ (f e).2.1 = e.2.1)
    (h : VarsOK ρ η σs vars env) : VarsOK ρ η σs (vars.map f) env := by
  intro x e he
  rw [find_map_flags vars f (fun e => (hf e).1) x] at he
  cases hfe : vars.find? (·.1 == x) with
  | none => simp [hfe] at he
  | some e0 =>
      simp only [hfe, Option.map_some, Option.some.injEq] at he
      subst he
      obtain ⟨rt, ws, hl, hiv, hs⟩ := h x e0 hfe
      exact ⟨rt, ws, hl, by rw [(hf e0).2]; exact hiv, by rw [(hf e0).2]; exact hs⟩

/-- `use` only flips a flag. -/
theorem use_inv {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx c₁ : Cx} {env : Env} {a : At} {t : Ty}
    (h : cx.use a = .ok (t, c₁)) :
    cx.peek a = .ok t ∧ c₁.facts = cx.facts ∧ c₁.ret = cx.ret ∧ (VarsOK ρ η σs cx.vars env → VarsOK ρ η σs c₁.vars env) := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨t', ht, h⟩ := h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ht, rfl, rfl, VarsOK_flags _ ?_⟩
      intro e; split <;> simp
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, rfl, rfl, id⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ht, rfl, rfl, id⟩

theorem use_opq {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) :
    c₁.opq = cx.opq ∧ c₁.ke = cx.ke := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨t', ht, h⟩ := h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem use_FInv {K : TEnv → List Word → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx c₁ : Cx} {env : Env} {a : At} {t : Ty}
    (h : cx.use a = .ok (t, c₁)) (hi : FInv ρ η σs K cx env) :
    FInv ρ η σs K c₁ env ∧ ∃ rt ws, evalAt env a = some (rt, ws) ∧ VR ρ η t (shp rt) ws ∧ Lay σs t rt ws := by
  obtain ⟨hp, hf, hr, hv⟩ := use_inv (ρ := ρ) (η := η) (env := env) h
  exact ⟨⟨hf ▸ hi.1, hv hi.2.1, by rw [hr, (use_opq h).1, (use_opq h).2]; exact hi.2.2⟩, peek_VR hi.2.1 hp⟩

theorem bind_eq {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    c' = { cx with vars := (x, t, true) :: cx.vars } := by
  unfold Cx.bind at h
  split at h <;> split at h <;> (try split at h) <;>
    simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem use_ret {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) : c₁.ret = cx.ret := by
  unfold Cx.use at h
  simp only [bind_ok_iff] at h
  obtain ⟨t1, _, h⟩ := h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

theorem bind_ret {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') : c'.ret = cx.ret := by
  rw [bind_eq h]

theorem fenceCx_ret (cx : Cx) (f : Fence) : (fenceCx cx f).ret = cx.ret := by
  unfold fenceCx
  split <;> split <;> rfl

theorem observeCx_ret (cx : Cx) (x w : String) (acq : Bool) :
    (observeCx cx x w acq).ret = cx.ret.shiftI 0 := rfl

theorem endCx_ret (cx : Cx) (y : String) : (cx.endCx y).ret = cx.ret := rfl

theorem push_ret (cx : Cx) (n : String) : (cx.push n).ret = cx.ret.shiftI 0 := rfl

theorem OpT_ret3 {p : Prog} {cx c' : Cx} {x : String} {op : Op} (h : OpT p cx x op c') :
    c'.ret = cx.ret ∨ c'.ret = cx.ret.shiftI 0 ∨ c'.ret = (cx.ret.shiftI 0).shiftI 0 := by
  cases h <;> first
    | exact Or.inl rfl
    | (obtain rfl := bind_eq ‹_›
       dsimp only
       first
        | exact Or.inl rfl
        | exact Or.inl (use_ret ‹_›)
        | exact Or.inl ((use_ret ‹_›).trans (use_ret ‹_›))
        | exact Or.inl (fenceCx_ret _ _)
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr rfl))

theorem OpT_retSk {p : Prog} {cx c' : Cx} {x : String} {op : Op} (h : OpT p cx x op c') :
    skel c'.ret = skel cx.ret := by
  rcases OpT_ret3 h with e | e | e <;> rw [e] <;> simp only [skel_shiftI]

theorem NoCx_retSk {cx c' : Cx} {i j : Idx} (h : NoCx cx i j c') : skel c'.ret = skel cx.ret := by
  cases h with
  | same => rfl
  | nzL _ _ => exact skel_shiftI cx.ret 0
  | nzR _ _ => exact skel_shiftI cx.ret 0

theorem bind_FInv {K : TEnv → List Word → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx c' : Cx} {env : Env} {x : String} {t rt : Ty}
    {ws : List Word} (h : cx.bind x t = .ok c') (hi : FInv ρ η σs K cx env) (hw : VR ρ η t (shp rt) ws)
    (hs : Lay σs t rt ws) : FInv ρ η σs K c' ((x, rt, ws) :: env) := by
  have hc := bind_eq h
  subst hc
  refine ⟨hi.1, ?_, hi.2.2⟩
  intro y e he
  simp only [List.find?_cons] at he
  by_cases hxy : x = y
  · subst hxy
    simp at he; subst he
    exact ⟨rt, ws, by simp [lookupE], hw, hs⟩
  · have hb : (x == y) = false := by simpa using hxy
    simp only [hb] at he
    obtain ⟨rt', ws', hl, hiv, hs'⟩ := hi.2.1 y e he
    refine ⟨rt', ws', ?_, hiv, hs'⟩
    simp only [lookupE, List.find?_cons, hb] at hl ⊢
    exact hl

/-! ### `push` and new facts -/

theorem lookup_shift (fs : Facts) :
    ∀ k, (fs.map fun (p : Nat × Idx) => (p.1 + 1, p.2.shift 0)).lookup k =
      match k with
      | 0 => none
      | k + 1 => (fs.lookup k).map (Idx.shift 0) := by
  induction fs with
  | nil => intro k; cases k <;> rfl
  | cons f rest ih =>
      intro k
      obtain ⟨k0, t0⟩ := f
      cases k with
      | zero =>
          have := ih 0
          simp only [List.map_cons, List.lookup_cons] at this ⊢
          simpa using this
      | succ k =>
          have := ih (k + 1)
          simp only [List.map_cons, List.lookup_cons] at this ⊢
          by_cases hk : k = k0
          · subst hk; simp
          · have h1 : (k + 1 == k0 + 1) = false := by simpa using hk
            have h2 : (k == k0) = false := by simpa using hk
            simp only [h1, h2]; exact this

theorem Sat_push {fs : Facts} {ρ : Nat → Nat} (w : Nat) (h : Sat fs ρ) :
    Sat (fs.map fun (p : Nat × Idx) => (p.1 + 1, p.2.shift 0)) (vcons w ρ) := by
  intro k t hk
  rw [lookup_shift] at hk
  cases k with
  | zero => simp at hk
  | succ k =>
      simp only at hk
      cases hl : fs.lookup k with
      | none => simp [hl] at hk
      | some t0 =>
          simp only [hl, Option.map_some, Option.some.injEq] at hk
          subst hk
          rw [vcons_succ, ev_shift, h k t0 hl]

/-- A new index variable: the return type is shifted with everything else. -/
theorem RetOK_push {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty} {K : TEnv → List Word → Prop} (w : Nat)
    (h : RetOK ρ η σs ret K) : RetOK (vcons w ρ) η σs (ret.shiftI 0) K := by
  intro η' he ws hv hl
  have e := skel_close_shiftI σs ret 0
  rw [shp_of_skel e] at hv
  refine h η' he ws ((VR_shift η' ret 0 w ρ _ ws).1 hv) ⟨ShapeC_wc (wc_of_skel e) hl.1, rfl, ?_, Valid_of_skel e hl.2.2.2.1, rfl⟩
  rw [← wc_of_skel e]; exact hl.2.2.1

theorem push_FInv {K : TEnv → List Word → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} (n : String) (w : Nat)
    (hi : FInv ρ η σs K cx env) : FInv (vcons w ρ) η σs K (cx.push n) env := by
  refine ⟨?_, ?_, RetOK_push w hi.2.2.1, hi.2.2.2⟩
  · simp only [Cx.push]
    exact Sat_push w hi.1
  · intro x e he
    simp only [Cx.push] at he
    rw [find_map_flags _ (fun (y, t, b) => (y, t.shiftI 0, b)) (fun _ => rfl)] at he
    cases hfe : cx.vars.find? (·.1 == x) with
    | none => simp [hfe] at he
    | some e0 =>
        simp only [hfe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨rt, ws, hl, hiv, hs⟩ := hi.2.1 x e0 hfe
        exact ⟨rt, ws, hl, (VR_shift η e0.2.1 0 w ρ (shp rt) ws).2 hiv, Lay_shiftI 0 hs⟩

/-! ### (P3) Holdings through `use`, `bind` and `push` -/

/-- Marking variable `y` used. -/
def markU (y : String) (e : String × Ty × Bool) : String × Ty × Bool :=
  if e.1 == y then (e.1, e.2.1, false) else e

theorem use_cases {cx c₁ : Cx} {a : At} {t : Ty} (h : cx.use a = .ok (t, c₁)) :
    cx.peek a = .ok t ∧ ((affine cx.ke t = false ∧ c₁ = cx) ∨
      ∃ y, a = .var y ∧ c₁ = { cx with vars := cx.vars.map (markU y) }) := by
  cases a with
  | var y =>
      unfold Cx.use at h
      simp only [bind_ok_iff] at h
      obtain ⟨t', ht, h⟩ := h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨ht, Or.inr ⟨y, rfl, ?_⟩⟩
        congr 1
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i hna
        exact ⟨ht, Or.inl ⟨by simpa using hna, rfl⟩⟩
  | lit n =>
      simp [Cx.use, Cx.peek, pure, Except.pure, bind, Except.bind] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  | unit =>
      simp [Cx.use, Cx.peek, pure, Except.pure, bind, Except.bind] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem peek_var {cx : Cx} {y : String} {t : Ty} (h : cx.peek (.var y) = .ok t) :
    cx.vars.find? (·.1 == y) = some (y, t, true) := by
  simp only [Cx.peek, Cx.find, bind_ok_iff] at h
  obtain ⟨⟨t', b⟩, hf, h⟩ := h
  cases hfe : cx.vars.find? (·.1 == y) with
  | none => simp [hfe, throw, throwThe, MonadExceptOf.throw] at hf
  | some e =>
      obtain ⟨z, u, b'⟩ := e
      simp only [hfe, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hz : z = y := by simpa using List.find?_some hfe
      subst hz
      cases b' <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem bind_fresh {cx c' : Cx} {x : String} {t : Ty} (h : cx.bind x t = .ok c') :
    ∀ e ∈ cx.vars, e.1 ≠ x := by
  intro e he hx
  unfold Cx.bind at h
  have : cx.vars.any (·.1 == x) = true := List.any_eq_true.2 ⟨e, he, by simp [hx]⟩
  simp [this, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-! Sums over held variables. -/

theorem sum_filter_congr (H H' : String × Ty × Bool → Bool) (Rx Rx' : String → Res) :
    ∀ l : List (String × Ty × Bool), (∀ e ∈ l, H e = H' e ∧ Rx e.1 = Rx' e.1) →
      Res.sum ((l.filter H).map (fun e => Rx e.1)) = Res.sum ((l.filter H').map (fun e => Rx' e.1))
  | [], _ => rfl
  | e :: l, h => by
      have ih := sum_filter_congr H H' Rx Rx' l (fun e he => h e (List.mem_cons_of_mem _ he))
      have he := h e List.mem_cons_self
      simp only [List.filter_cons, he.1]
      split <;> simp [ih, he.2]

/-- Marking a held, unlent `y` used removes exactly its resources. -/
theorem sum_markU (lent : List String) (Rx : String → Res) (y : String) (hy : y ∉ lent) :
    ∀ l : List (String × Ty × Bool), (l.map (·.1)).Nodup → (∃ t, (y, t, true) ∈ l) →
      Res.sum (((l.map (markU y)).filter (fun e => e.2.2 || decide (e.1 ∈ lent))).map (fun e => Rx e.1)) + Rx y =
        Res.sum ((l.filter (fun e => e.2.2 || decide (e.1 ∈ lent))).map (fun e => Rx e.1))
  | [], _, ⟨_, h⟩ => absurd h List.not_mem_nil
  | e :: l, hn, ⟨t, ht⟩ => by
      obtain ⟨z, u, b⟩ := e
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      by_cases hz : z = y
      · subst hz
        -- `e` is the held entry; the rest has no `z`.
        have hb : b = true := by
          rcases List.mem_cons.1 ht with h | h
          · simp at h; exact h.2
          · exact absurd ⟨_, h, rfl⟩ hn.1
        subst hb
        have hrest : ∀ e ∈ l, markU z e = e := by
          intro e he; simp only [markU]
          have : (e.1 == z) = false := by simp; intro h; exact hn.1 ⟨e, he, h⟩
          simp [this]
        simp only [List.map_cons]
        rw [List.map_congr_left hrest, List.map_id']
        simp [markU, hy, Res.add_comm]
      · have hrest : ∃ t, (y, t, true) ∈ l := by
          rcases List.mem_cons.1 ht with h | h
          · simp at h; exact absurd h.1.symm hz
          · exact ⟨t, h⟩
        have ih := sum_markU lent Rx y hy l hn.2 hrest
        have hm : markU y (z, u, b) = (z, u, b) := by simp [markU, hz]
        simp only [List.map_cons, hm, List.filter_cons]
        split
        · simp only [List.map_cons, Res.sum_cons, Res.add_assoc, ih]
        · exact ih

theorem mem_nodup_eq : ∀ (l : List (String × Ty × Bool)), (l.map (·.1)).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a = b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, hn, a, ha, b, hb, hab => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
      · rw [h1, h2]
      · subst h1; exact absurd ⟨b, h2, hab.symm⟩ hn.1
      · subst h2; exact absurd ⟨a, h1, hab⟩ hn.1
      · exact mem_nodup_eq l hn.2 a h1 b h2 hab

/-! The frame-holding lemmas. -/

/-- **Using an atom** hands over its resources: the value carries `R`, the
frame keeps `Rr`, and together they fit in what the frame had. -/
theorem use_HeldOK {ρ : Nat → Nat} {η : TEnv} {cx c₁ : Cx} {env : Env} {a : At} {t : Ty} {Rf : Res}
    (h : cx.use a = .ok (t, c₁)) (hH : HeldOK ρ η cx env Rf) (hw : WitC cx.ke η) (hr : CohR η) :
    ∃ rt ws R Rr, evalAt env a = some (rt, ws) ∧ VRR ρ η t (shp rt) ws R ∧ HeldOK ρ η c₁ env Rr ∧
      R + Rr ≤ Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := hH
  obtain ⟨hp, hc⟩ := use_cases h
  -- The value and its resources, read from the frame.
  have hval : ∃ rt ws R, evalAt env a = some (rt, ws) ∧ VRR ρ η t (shp rt) ws R ∧
      ∀ y, a = .var y → R = Rx y := by
    cases a with
    | var y =>
        have hf := peek_var hp
        obtain ⟨rt, ws, hl, hv⟩ := hx y _ hf (by simp [Holds])
        exact ⟨rt, ws, Rx y, hl, hv, fun y' e => by cases e; rfl⟩
    | lit n =>
        simp [Cx.peek, pure, Except.pure] at hp; subst hp
        exact ⟨_, _, .zero, rfl, ⟨rfl, rfl⟩, fun _ e => by cases e⟩
    | unit =>
        simp [Cx.peek, pure, Except.pure] at hp; subst hp
        exact ⟨_, _, .zero, rfl, by simp [VRR], fun _ e => by cases e⟩
  obtain ⟨rt, ws, R, he, hv, hRy⟩ := hval
  rcases hc with ⟨hna, rfl⟩ | ⟨y, rfl, rfl⟩
  · -- Not affine: nothing moves.
    have h0 : R = .zero := VRR_copy_frame hw hr hna hv
    subst h0
    exact ⟨rt, ws, .zero, Rf, he, hv, ⟨hn, hln, hlent, Rx, hx, hs⟩, by simp; exact Res.le_refl _⟩
  · -- Affine: `y` is marked used and its resources leave the frame.
    have hf := peek_var hp
    have hyl : y ∉ cx.lent := by
      intro hm
      obtain ⟨e, he1, rfl, hb, -⟩ := hlent _ hm
      have h1 := List.mem_of_find?_eq_some hf
      have : e = (e.1, t, true) := mem_nodup_eq cx.vars hn e he1 _ h1 rfl
      rw [this] at hb; cases hb
    have hR := hRy y rfl
    subst hR
    refine ⟨rt, ws, Rx y, Res.sum ((((cx.vars.map (markU y)).filter
      (fun e => e.2.2 || decide (e.1 ∈ cx.lent))).map (fun e => Rx e.1))), he, hv, ⟨?_, hln, ?_, Rx, ?_, Res.le_refl _⟩, ?_⟩
    · show ((cx.vars.map (markU y)).map (·.1)).Nodup
      rw [List.map_map]
      have : ((·.1) ∘ markU y) = (·.1 : String × Ty × Bool → String) := by
        funext e; simp only [Function.comp, markU]; split <;> rfl
      rw [this]; exact hn
    · intro z hz
      obtain ⟨e, he1, h1, h2, h3⟩ := hlent z hz
      refine ⟨markU y e, List.mem_map_of_mem he1, ?_, ?_, ?_⟩ <;> simp only [markU] <;> split <;> simp_all
    · intro z e hfe hh
      show ∃ rt ws, lookupE env z = some (rt, ws) ∧ VRR ρ η e.2.1 (shp rt) ws (Rx z)
      have hfe' := hfe
      simp only at hfe'
      rw [find_map_flags _ (markU y) (fun e => by simp only [markU]; split <;> rfl)] at hfe'
      cases hf0 : cx.vars.find? (·.1 == z) with
      | none => simp [hf0] at hfe'
      | some e0 =>
          simp only [hf0, Option.map_some, Option.some.injEq] at hfe'
          subst hfe'
          have hh0 : Holds cx e0 = true := by
            simp only [Holds, markU] at hh ⊢
            split at hh <;> simp_all
          have ht : (markU y e0).2.1 = e0.2.1 := by simp only [markU]; split <;> rfl
          rw [ht]
          exact hx z e0 hf0 hh0
    · rw [Res.add_comm, sum_markU cx.lent Rx y hyl cx.vars hn ⟨t, List.mem_of_find?_eq_some hf⟩]
      exact hs

/-- **Binding** a value carrying `R` adds `R` to the frame. -/
theorem bind_HeldOK {ρ : Nat → Nat} {η : TEnv} {cx c' : Cx} {env : Env} {x : String} {t rt : Ty}
    {ws : List Word} {R Rf : Res} (h : cx.bind x t = .ok c') (hH : HeldOK ρ η cx env Rf)
    (hv : VRR ρ η t (shp rt) ws R) : HeldOK ρ η c' ((x, rt, ws) :: env) (Rf + R) := by
  have hfr := bind_fresh h
  have hc := bind_eq h
  subst hc
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := hH
  let Rx' : String → Res := fun z => if z = x then R else Rx z
  refine ⟨?_, hln, ?_, Rx', ?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons, List.mem_map]
    exact ⟨fun ⟨e, he, hx'⟩ => hfr e he hx', hn⟩
  · intro y hy
    obtain ⟨e, he, h1, h2⟩ := hlent y hy
    exact ⟨e, List.mem_cons_of_mem _ he, h1, h2⟩
  · intro z e hfe hh
    simp only [List.find?_cons] at hfe
    by_cases hxz : x = z
    · subst hxz
      simp at hfe; subst hfe
      exact ⟨rt, ws, by simp [lookupE], by simp [Rx', hv]⟩
    · have hb : (x == z) = false := by simpa using hxz
      simp only [hb] at hfe
      have hh' : Holds cx e = true := hh
      obtain ⟨rt', ws', hl, hv'⟩ := hx z e hfe hh'
      refine ⟨rt', ws', ?_, ?_⟩
      · simp only [lookupE, List.find?_cons, hb] at hl ⊢; exact hl
      · have : z ≠ x := fun e => hxz e.symm
        simpa [Rx', this] using hv'
  · show Res.sum ((((x, t, true) :: cx.vars).filter (Holds { cx with vars := (x, t, true) :: cx.vars })).map
      (fun e => Rx' e.1)) ≤ Rf + R
    have e1 : Res.sum ((cx.vars.filter (Holds { cx with vars := (x, t, true) :: cx.vars })).map (fun e => Rx' e.1)) =
        Res.sum ((cx.vars.filter (Holds cx)).map (fun e => Rx e.1)) :=
      sum_filter_congr _ _ _ _ cx.vars (fun e he => ⟨rfl, by simp [Rx', hfr e he]⟩)
    have hx0 : Holds { cx with vars := (x, t, true) :: cx.vars } (x, t, true) = true := by simp [Holds]
    have hR : Rx' x = R := by simp [Rx']
    rw [List.filter_cons_of_pos hx0, List.map_cons, Res.sum_cons, e1, hR, Res.add_comm]
    exact Res.add_le_add hs (Res.le_refl _)

/-- **A new index variable** shifts every type; holdings are unchanged. -/
theorem push_HeldOK {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf : Res} (n : String) (w : Nat)
    (hH : HeldOK ρ η cx env Rf) : HeldOK (vcons w ρ) η (cx.push n) env Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := hH
  let f : String × Ty × Bool → String × Ty × Bool := fun (y, t, b) => (y, t.shiftI 0, b)
  have hf1 : ∀ e, (f e).1 = e.1 := fun _ => rfl
  have hHf : ∀ e, Holds (cx.push n) (f e) = Holds cx e := fun _ => rfl
  refine ⟨?_, hln, ?_, Rx, ?_, ?_⟩
  · show ((cx.vars.map f).map (·.1)).Nodup
    rw [List.map_map]; exact hn
  · intro y hy
    obtain ⟨⟨y', t', b'⟩, he, h1, h2, h3⟩ := hlent y hy
    exact ⟨f (y', t', b'), List.mem_map_of_mem he, h1, h2, by simpa [f, secondClass_shiftI] using h3⟩
  · intro x e hfe hh
    simp only [Cx.push] at hfe
    rw [find_map_flags _ f hf1] at hfe
    cases hf0 : cx.vars.find? (·.1 == x) with
    | none => simp [hf0] at hfe
    | some e0 =>
        simp only [hf0, Option.map_some, Option.some.injEq] at hfe
        subst hfe
        obtain ⟨rt, ws, hl, hv⟩ := hx x e0 hf0 (by rw [← hHf e0]; exact hh)
        exact ⟨rt, ws, hl, (VRR_shift η e0.2.1 0 w ρ (shp rt) ws (Rx x)).2 hv⟩
  · show Res.sum (((cx.vars.map f).filter (Holds (cx.push n))).map (fun e => Rx e.1)) ≤ Rf
    rw [List.filter_map, List.map_map]
    have : (Holds (cx.push n) ∘ f) = Holds cx := funext hHf
    rw [this]
    exact hs


/-- **A new type variable** (24e `unpackT`): any relation and witness for it
(T3c: `unpackT` uses the package's witness, coherently), and the frame's type
arguments get `Unit` for it, which no layout reads. -/
theorem sig_close_cons (σ : Ty) (σs : List Ty) (j : Nat) :
    sig (close (σ :: σs) (.tvar (j + 1))) = sig (close σs (.tvar j)) := by
  simp only [close, substTs, Nat.not_lt_zero, if_false, Nat.sub_zero, List.getElem?_cons_succ]
  cases σs[j]? <;> rfl

theorem accs_close_cons (σ : Ty) (σs : List Ty) (j : Nat) :
    accs (close (σ :: σs) (.tvar (j + 1))) = accs (close σs (.tvar j)) := by
  simp only [close, substTs, Nat.not_lt_zero, ite_false, Nat.sub_zero, List.getElem?_cons_succ]
  cases σs[j]? <;> rfl

theorem pushT_FInv {K : TEnv → List Word → Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} (κ : Kind)
    (s : Ty) (hc : Coh η) (hs : Clo s) (haf : WitOK κ s)
    (hi : FInv ρ η σs K cx env) : FInv ρ (η.consC s) (.unit :: σs) K (cx.pushT κ) env := by
  let R := η.relC s
  refine ⟨hi.1, ?_, ?_, ?_, ?_⟩
  · intro x e he
    simp only [Cx.pushT] at he
    rw [find_map_flags _ (fun (y, t, b) => (y, t.shiftT 0, b)) (fun _ => rfl)] at he
    cases hfe : cx.vars.find? (·.1 == x) with
    | none => simp [hfe] at he
    | some e0 =>
        simp only [hfe, Option.map_some, Option.some.injEq] at he
        subst he
        obtain ⟨rt, ws, hl, hiv, hs⟩ := hi.2.1 x e0 hfe
        refine ⟨rt, ws, hl, VR_insR_rr.2 ((VR_shiftTU e0.2.1 0 η R s (η.unsee.relC s) ρ (shp rt) ws).2 hiv), hs.1, ?_, hs.2.2.1, hs.2.2.2.1, ?_⟩
        · rw [hs.2.1]; unfold close; rw [substTs_cons_shiftT]
        · rw [hs.2.2.2.2]; unfold close; rw [substTs_cons_shiftT]
  · intro η' he ws hv hl
    have e : close (.unit :: σs) (cx.ret.shiftT 0) = close σs cx.ret := substTs_cons_shiftT _ _ _ 0 0
    simp only [Cx.pushT] at hv hl
    rw [e] at hv
    rw [e] at hl
    let η'' := η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box η'.rid η'.fp η'.rini
    have h2 : Ext η η'' := Ext_withSto hc (fun l c h => he.2.2.2.2.1 l c h) he.2.2.2.2.2.1 he.2.2.2.2.2.2.1
      he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.2.1 η'.fp η'.rini he.rini
    have hC : CE η'' = CE η' := by
      have hp : η'.prog = η.prog := he.2.2.1
      have ht : η'.tid = η.tid := he.2.2.2.1
      simp only [CE, η'', TEnv.withSto, hp, ht]
    have hv' : VR ρ (η''.consC s) (cx.ret.shiftT 0) (shp (close σs cx.ret)) ws :=
      (VR_coh (Coh_consC h2.1 hs) he.1 he.2.1.symm hC ρ _ _ ws).2 hv
    have h3 := hi.2.2.1 η'' h2 ws ((VR_shiftTU cx.ret 0 η'' (η''.relC s) s (η''.unsee.relC s) ρ _ ws).1 (VR_insR_rr.1 hv')) ⟨hl.1, rfl, hl.2.2.1, hl.2.2.2.1, rfl⟩
    rw [← hC]; exact h3
  · refine ⟨fun k hk => ?_, fun k σ hσ => ?_, fun k hk => ?_⟩
    · cases k with
      | zero => simp [Cx.pushT] at hk
      | succ j =>
          have hj : j ∉ cx.opq := by intro h; apply hk; simp [Cx.pushT, h]
          intro hl
          show sig (close (.unit :: σs) (.tvar (j + 1))) = sig (η.wit j)
          rw [sig_close_cons]; exact hi.2.2.2.1.1 j hj (by simpa using hl)
    · cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hσ; subst hσ
          exact ⟨fun h => absurd (by simp [Cx.pushT] : 0 ∈ (cx.pushT κ).opq) h, fun _ => rfl⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hσ
          have e : (j + 1 ∈ (cx.pushT κ).opq) ↔ j ∈ cx.opq := by simp [Cx.pushT]
          rw [e]
          exact hi.2.2.2.1.2.1 j σ hσ
    · cases k with
      | zero => simp [Cx.pushT] at hk
      | succ j =>
          have hj : j ∉ cx.opq := by intro h; apply hk; simp [Cx.pushT, h]
          intro hl
          show accs (close (.unit :: σs) (.tvar (j + 1))) = accs (η.wit j)
          rw [accs_close_cons]; exact hi.2.2.2.1.2.2 j hj (by simpa using hl)
  · refine ⟨?_, KindsOK_pushT κ hi.2.2.2.2.2.1, ?_⟩
    · show (some κ :: cx.ke).length ≤ (Ty.unit :: σs).length
      simp only [List.length_cons]; exact Nat.succ_le_succ hi.2.2.2.2.1
    · refine ⟨fun k => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · cases k with
        | zero => simpa [TEnv.consC, TEnv.insR] using And.intro haf.1 (And.intro haf.2.2.2.2.2.1 haf.2.2.2.2.2.2)
        | succ k => simpa [TEnv.consC, TEnv.insR] using hi.2.2.2.2.2.2.1 k
      · cases k with
        | zero => simpa [TEnv.consC, TEnv.insR] using haf.2.1 (by simpa [Cx.pushT, KEnv.ask] using hk)
        | succ k => simpa [TEnv.consC, TEnv.insR] using hi.2.2.2.2.2.2.2.1 k (by simpa [Cx.pushT, KEnv.ask] using hk)
      · cases k with
        | zero => simpa [TEnv.consC, TEnv.insR] using haf.2.2.1 (by simpa [Cx.pushT, KEnv.ask] using hk)
        | succ k => simpa [TEnv.consC, TEnv.insR] using hi.2.2.2.2.2.2.2.2.1 k (by simpa [Cx.pushT, KEnv.ask] using hk)
      · cases k with
        | zero => simpa [TEnv.consC, TEnv.insR] using haf.2.2.2.1 (by simpa [Cx.pushT, KEnv.ask] using hk)
        | succ k => simpa [TEnv.consC, TEnv.insR] using hi.2.2.2.2.2.2.2.2.2.1 k (by simpa [Cx.pushT, KEnv.ask] using hk)
      · cases k with
        | zero => simpa [TEnv.consC, TEnv.insR] using haf.2.2.2.2.1 (by simpa [Cx.pushT, KEnv.ask] using hk)
        | succ k => simpa [TEnv.consC, TEnv.insR] using hi.2.2.2.2.2.2.2.2.2.2 k (by simpa [Cx.pushT, KEnv.ask] using hk)

theorem Sat_cons {fs : Facts} {ρ : Nat → Nat} {k : Nat} {t : Idx} (h : Sat fs ρ) (hk : ρ k = ev ρ t) :
    Sat ((k, t) :: fs) ρ := by
  intro k' t' hk'
  simp only [List.lookup_cons] at hk'
  by_cases e : k' = k
  · subst e; simp at hk'; subst hk'; exact hk
  · have : (k' == k) = false := by simpa using e
    simp only [this] at hk'
    exact h k' t' hk'

/-! ## §4 P1 and P4 for the pure operations -/

/-- A known-index integer atom: its one word, its value, and its layout. -/
theorem atom_num {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty} {i : Idx}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (hi : intOf t = some (some i)) :
    ∃ rt w, evalAt env a = some (rt, [w]) ∧ w.val = .num (ev ρ i) ∧ Lay σs t rt [w] := by
  obtain ⟨rt, ws, he, hiv, hs⟩ := peek_VR hv h
  obtain ⟨w, rfl, hw⟩ := map_singleton (VR_intS hi hiv)
  exact ⟨rt, w, he, hw, hs⟩

/-- Any integer atom: one `num` word. -/
theorem atom_int {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty} {o : Option Idx}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (hi : intOf t = some o) :
    ∃ rt w n, evalAt env a = some (rt, [w]) ∧ w.val = .num n := by
  obtain ⟨rt, ws, he, hiv, -⟩ := peek_VR hv h
  obtain ⟨n, hn⟩ := VR_int hi hiv
  obtain ⟨w, rfl, hw⟩ := map_singleton hn
  exact ⟨rt, w, n, he, hw⟩

/-- (E1) A `ThreadId` atom: one `num` word. -/
theorem atom_tid {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (ht : tidOf t = true) :
    ∃ rt w l, evalAt env a = some (rt, [w]) ∧ w.val = .loc ⟨l, 0⟩ 0 := by
  obtain ⟨rt, ws, he, hiv, -⟩ := peek_VR hv h
  have e : t = .tid := by cases t <;> simp [tidOf] at ht ⊢
  subst e
  simp only [VR] at hiv
  obtain ⟨l, c, hn, -⟩ := hiv
  obtain ⟨w, rfl, hw⟩ := map_singleton hn
  exact ⟨rt, w, l, he, hw⟩

/-- (E1) Both operands of a fact-free `ifeq` (`PlainEq`: integers, or `ThreadId`s) are one `num` word. -/
theorem atom_plainEq {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a b : At}
    (hv : VarsOK ρ η σs cx.vars env) (hpe : PlainEq cx a b) :
    ((∃ rt w n, evalAt env a = some (rt, [w]) ∧ w.val = .num n) ∧
      (∃ rt w n, evalAt env b = some (rt, [w]) ∧ w.val = .num n)) ∨
    ((∃ rt w l, evalAt env a = some (rt, [w]) ∧ w.val = .loc ⟨l, 0⟩ 0) ∧
      (∃ rt w l, evalAt env b = some (rt, [w]) ∧ w.val = .loc ⟨l, 0⟩ 0)) := by
  obtain ⟨ta, tb, hpa, hpb, hab⟩ := hpe
  rcases hab with ⟨hsa, hsb, -⟩ | ⟨hta, htb⟩
  · obtain ⟨oa, hoa⟩ := Option.isSome_iff_exists.1 hsa
    obtain ⟨ob, hob⟩ := Option.isSome_iff_exists.1 hsb
    exact Or.inl ⟨atom_int hv hpa hoa, atom_int hv hpb hob⟩
  · exact Or.inr ⟨atom_tid hv hpa hta, atom_tid hv hpb htb⟩

theorem fixOf_eq {t : Ty} {q : Bool × Wd} (h : fixOf t = some q) : t = .fix q.1 q.2 := by
  cases t <;> simp [fixOf] at h; subst h; rfl

theorem lanesOf_eq {t : Ty} {q : Bool × Wd} (h : lanesOf t = some q) : t = .lanes q.1 q.2 := by
  cases t <;> simp [lanesOf] at h; subst h; rfl

/-- A fixed-width atom: its runtime type is its static one, one `num` word below `2^w`. -/
theorem atom_fix {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty} {q : Bool × Wd}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (hq : fixOf t = some q) :
    ∃ w n, evalAt env a = some (.fix q.1 q.2, [w]) ∧ w.val = .num n ∧ n < pw2 q.2 := by
  obtain ⟨rt, ws, he, hiv, hl⟩ := peek_VR hv h
  have e : rt = .fix q.1 q.2 := eskel_eq_fix (by rw [hl.2.1, fixOf_eq hq]; rfl)
  subst e
  rw [fixOf_eq hq] at hiv
  obtain ⟨-, n, hn, hb⟩ := hiv
  obtain ⟨w, rfl, hw⟩ := map_singleton hn
  exact ⟨w, n, he, hw, hb⟩

theorem atom_lanes {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty} {q : Bool × Wd}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (hq : lanesOf t = some q) :
    ∃ w n, evalAt env a = some (.lanes q.1 q.2, [w]) ∧ w.val = .num n := by
  obtain ⟨rt, ws, he, hiv, hl⟩ := peek_VR hv h
  have e : rt = .lanes q.1 q.2 := eskel_eq_lanes (by rw [hl.2.1, lanesOf_eq hq]; rfl)
  subst e
  rw [lanesOf_eq hq] at hiv
  obtain ⟨-, n, hn⟩ := hiv
  obtain ⟨w, rfl, hw⟩ := map_singleton hn
  exact ⟨w, n, he, hw⟩

/-- Any atom `cvt` or `toInt` reads: one `num` word. -/
theorem atom_cvt {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    (hv : VarsOK ρ η σs cx.vars env) (h : cx.peek a = .ok t) (hc : cvtSrc t = true) :
    ∃ rt w n, evalAt env a = some (rt, [w]) ∧ w.val = .num n := by
  simp only [cvtSrc, Bool.or_eq_true, Option.isSome_iff_exists] at hc
  rcases hc with (⟨o, ho⟩ | ⟨q, hq⟩) | ⟨q, hq⟩
  · exact atom_int hv h ho
  · obtain ⟨w, n, he, hw, -⟩ := atom_fix hv h hq; exact ⟨_, w, n, he, hw⟩
  · obtain ⟨w, n, he, hw⟩ := atom_lanes hv h hq; exact ⟨_, w, n, he, hw⟩

theorem toIntSrc_cvt {t : Ty} (h : toIntSrc t = true) : cvtSrc t = true := by
  cases t <;> simp_all [toIntSrc, cvtSrc, fixOf, lanesOf, intOf]

def PackOK : Ty → Prop
  | .iex _ => True
  | _ => False

/-- (S7) The scope's check at `packT` (until R2): a `share` witness is
region-free.  Checked at the instantiation, so polymorphic bodies stay in. -/
def PackTOK (σ : Ty) : Ty → Prop
  | .tex κ _ => κ.share = true → rgnFree σ = true
  | _ => True

/-- The fragment covered so far: arithmetic, pairs, and packing. -/
def PureOp : Op → Prop
  | .atom _ | .add _ _ | .sub _ _ | .nameI _ | .rem _ _ | .pair _ _ => True
  | .bits _ _ _ | .bit1 _ _ | .vmatch _ _ _ | .band _ _ => True
  | .cvt _ _ _ | .toInt _ | .asLanes _ _ _ | .fop _ _ _ | .fcmp _ _ _ | .fop1 _ _ => True
  | .lane _ _ | .setLane _ _ _ => True
  | .pack _ _ τ => PackOK τ
  | .packT _ σ τ => PackTOK σ τ ∧ noIallV σ = true
  | _ => False

/-! ### Type-argument substitution (moved before `pure_pres`, which uses it) -/

theorem VR_shiftIN (η : TEnv) (σ : Ty) (rt : Shp) (ws : List Word) :
    ∀ (d : Nat) (ρ : Nat → Nat), VR ρ η (shiftIN d σ) rt ws ↔ VR (fun k => ρ (k + d)) η σ rt ws
  | 0, ρ => by simp [shiftIN]
  | d + 1, ρ => by
      have h := VR_shift η (shiftIN d σ) 0 (ρ 0) (fun k => ρ (k + 1)) rt ws
      rw [vcons_eta] at h
      simp only [shiftIN]
      rw [h, VR_shiftIN η σ rt ws d]
      have : (fun k => ρ (k + d + 1)) = (fun k => ρ (k + (d + 1))) := by funext k; rfl
      simp only [Nat.add_assoc] at this ⊢

/-- The callee's `η`: its type variables are the caller's type arguments, read
by the caller's `VR` (on values), with the caller's closure of each argument as
the witness; the rest is the caller's `η`. -/
def subE (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : TEnv where
  rels k := match σs[k]? with
    | some σ => fun rt ws => VR ρ₀ η σ rt ws
    | none => η.rels (k - σs.length)
  urels k := match σs[k]? with
    | some σ => fun rt ws => VR ρ₀ η.unsee σ rt ws
    | none => η.urels (k - σs.length)
  rrs k := match σs[k]? with
    | some σ => fun rt ws X => VRR ρ₀ η σ rt ws X
    | none => η.rrs (k - σs.length)
  urrs k := match σs[k]? with
    | some σ => fun rt ws X => VRR ρ₀ η.unsee σ rt ws X
    | none => η.urrs (k - σs.length)
  wit k := match σs[k]? with
    | some σ => cl ρ₀ η.wit 0 0 σ
    | none => η.wit (k - σs.length)
  prog := η.prog
  sto := η.sto
  tid := η.tid
  ini := η.ini
  pfr := η.pfr
  seen := η.seen
  box := η.box
  rid := η.rid
  fp := η.fp
  rini := η.rini

theorem subE_unsee (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) :
    (subE ρ₀ η σs).unsee = subE ρ₀ η.unsee σs := rfl

theorem subE_box (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).box = η.box := rfl

theorem subE_prog (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).prog = η.prog := rfl
theorem subE_sto (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).sto = η.sto := rfl
theorem subE_tid (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).tid = η.tid := rfl
theorem subE_ini (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).ini = η.ini := rfl
theorem subE_rini (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).rini = η.rini := rfl

theorem TEnv.ownTop_substTs (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) (P : List Ty) (d : Nat) (t : Ty) :
    (TEnv.pre P η).ownTop (substTs σs P.length d t) = (TEnv.pre P (subE ρ₀ η σs)).ownTop t := by
  cases t with
  | tvar k =>
      simp only [substTs]
      by_cases hkc : k < P.length
      · simp only [hkc, ↓reduceIte]; exact congrArg Ty.ownHead (pre_wit_lt η (subE ρ₀ η σs) P k hkc)
      · simp only [hkc, ↓reduceIte]
        have hw := pre_wit_ge (subE ρ₀ η σs) P k (by omega)
        cases hk : σs[k - P.length]? with
        | some σ =>
            dsimp only
            rw [TEnv.ownTop_shiftIN, TEnv.ownTop_shiftTN]
            show η.ownTop σ = ((TEnv.pre P (subE ρ₀ η σs)).wit k).ownHead
            rw [hw]; simp only [subE, hk]; exact (TEnv.ownHead_cl0 η ρ₀ 0 σ).symm
        | none =>
            dsimp only
            have hl : σs.length ≤ k - P.length := by simpa using hk
            show ((TEnv.pre P η).wit (k - σs.length)).ownHead = ((TEnv.pre P (subE ρ₀ η σs)).wit k).ownHead
            rw [hw, pre_wit_ge η P _ (by omega)]
            simp only [subE, hk]
            rw [show k - σs.length - P.length = k - P.length - σs.length by omega]
  | loc μ _ => cases μ <;> rfl
  | ptr μ _ => cases μ <;> rfl
  | ptrOpt μ _ => cases μ <;> rfl
  | _ => rfl

theorem TEnv.selIni_substTs (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) (P : List Ty) (d : Nat) (t : Ty) :
    (TEnv.pre P η).selIni (substTs σs P.length d t) = (TEnv.pre P (subE ρ₀ η σs)).selIni t := by
  unfold TEnv.selIni; rw [TEnv.ownTop_substTs σs η ρ₀]; simp only [pre_ini, pre_rini, subE_ini, subE_rini]
theorem subE_pfr (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).pfr = η.pfr := rfl
theorem subE_seen (ρ₀ : Nat → Nat) (η : TEnv) (σs : List Ty) : (subE ρ₀ η σs).seen = η.seen := rfl

theorem subE_get_lt {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} {σ : Ty} (hk : σs[k]? = some σ) :
    (subE ρ₀ η σs).get k = fun S ws => VR ρ₀ η σ S ws := by
  simp only [TEnv.get, subE, hk]

theorem subE_get_ge {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} (hl : σs.length ≤ k) :
    (subE ρ₀ η σs).get k = η.get (k - σs.length) := by
  have : σs[k]? = none := List.getElem?_eq_none hl
  simp only [TEnv.get, subE, this]

theorem subE_rels_lt {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} {σ : Ty} (hk : σs[k]? = some σ) :
    (subE ρ₀ η σs).rels k = fun S ws => VR ρ₀ η σ S ws := by
  simp only [subE, hk]

theorem subE_rels_ge {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} (hl : σs.length ≤ k) :
    (subE ρ₀ η σs).rels k = η.rels (k - σs.length) := by
  have : σs[k]? = none := List.getElem?_eq_none hl
  simp only [subE, this]

theorem subE_wit_lt {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} {σ : Ty} (hk : σs[k]? = some σ) :
    (subE ρ₀ η σs).wit k = cl ρ₀ η.wit 0 0 σ := by
  simp only [subE, hk]

theorem subE_wit_ge {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} (hl : σs.length ≤ k) :
    (subE ρ₀ η σs).wit k = η.wit (k - σs.length) := by
  have : σs[k]? = none := List.getElem?_eq_none hl
  simp only [subE, this]

/-- The closures agree: substituting `σs` and closing in `η` is closing in the
callee's `η`. -/
theorem cl_subE (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) (P : List Ty) (d : Nat) (ρ : Nat → Nat)
    (hρ : ∀ k, ρ (k + d) = ρ₀ k) (t : Ty) :
    cl ρ (TEnv.pre P η).wit 0 0 (substTs σs P.length d t) = cl ρ (TEnv.pre P (subE ρ₀ η σs)).wit 0 0 t := by
  have hpre : ∀ k, k < P.length → (TEnv.pre P (subE ρ₀ η σs)).wit k = (TEnv.pre P η).wit k :=
    fun k hk => pre_wit_lt (subE ρ₀ η σs) η P k hk
  have hW : (fun k => (TEnv.pre P η).wit (k + P.length)) = η.wit := by
    funext k
    rw [pre_wit_ge η P (k + P.length) (by omega), Nat.add_sub_cancel]
  have hR : (fun k => ρ (k + d)) = ρ₀ := funext hρ
  have hsub : ∀ j σ, σs[j]? = some σ → (TEnv.pre P (subE ρ₀ η σs)).wit (P.length + j) =
      cl (fun k => ρ (k + d)) (fun k => (TEnv.pre P η).wit (k + P.length)) 0 0 σ := by
    intro j σ hj
    rw [pre_wit_ge _ P (P.length + j) (by omega), Nat.add_sub_cancel_left, subE_wit_lt hj, hW, hR]
  have hrest : ∀ k, (TEnv.pre P (subE ρ₀ η σs)).wit (P.length + σs.length + k) =
      (TEnv.pre P η).wit (P.length + k) := by
    intro k
    rw [pre_wit_ge _ P _ (by omega), pre_wit_ge η P _ (by omega),
      subE_wit_ge (by omega)]
    congr 1; omega
  have h := cl_substTs σs P.length d (ρ := ρ) hpre hsub hrest t 0 0
  simp only [Nat.add_zero] at h
  exact h

theorem VR_substTs (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) :
    ∀ (t : Ty) (P : List Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word), (∀ k, ρ (k + d) = ρ₀ k) →
      (VR ρ (TEnv.pre P η) (substTs σs P.length d t) rt ws ↔ VR ρ (TEnv.pre P (subE ρ₀ η σs)) t rt ws)
  | .tvar k, P, d, ρ, rt, ws, hρ => by
      simp only [substTs]
      by_cases hkc : k < P.length
      · simp only [hkc, if_true, VR, pre_get]
      · simp only [hkc, if_false]
        cases hk : σs[k - P.length]? with
        | some σ =>
            dsimp only
            rw [VR_shiftIN, VR_shiftTN]
            simp only [VR, pre_get, hkc, if_false, subE_get_lt hk]
            have : (fun k => ρ (k + d)) = ρ₀ := funext hρ
            rw [this]
            exact ⟨fun h => ⟨ws, WLe_refl ws, h⟩, fun ⟨ws', e, h⟩ => VR_up _ _ _ _ e h⟩
        | none =>
            dsimp only
            have hl : σs.length ≤ k - P.length := by simpa using hk
            have h1 : ¬ (k - σs.length < P.length) := by omega
            simp only [VR, pre_get, hkc, h1, if_false, subE_get_ge hl]
            rw [show k - σs.length - P.length = k - P.length - σs.length by omega]
  | .refine t ψ, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR, pre_ini, subE_ini]; exact and_congr (VR_substTs σs η ρ₀ t P d ρ rt ws hρ) (by rw [TEnv.selIni_substTs σs η ρ₀])
  | .iex b, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      exact VR_substTs σs η ρ₀ b P (d + 1) (vcons v ρ) rb ws (fun k => by rw [← Nat.add_assoc, vcons_succ]; exact hρ k)
  | .prod a b, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR]
      refine exists_congr fun ra => exists_congr fun rb => and_congr_right fun _ =>
        forall_congr' fun n => imp_congr_right fun _ => and_congr_right fun _ => ?_
      rw [VR_substTs σs η ρ₀ a P d ρ _ _ hρ, VR_substTs σs η ρ₀ b P d ρ _ _ hρ]
  | .sum a b, P, d, ρ, rt, ws, hρ => by
      have ha := fun rt ws => VR_substTs σs η ρ₀ a P d ρ rt ws hρ
      have hb := fun rt ws => VR_substTs σs η ρ₀ b P d ρ rt ws hρ
      have hau := fun rt ws => VR_substTs σs η.unsee ρ₀ a P d ρ rt ws hρ
      have hbu := fun rt ws => VR_substTs σs η.unsee ρ₀ b P d ρ rt ws hρ
      simp only [substTs, VR, pre_box, pre_tid, pre_seen, pre_pfr, subE_box, subE_tid, subE_seen, subE_pfr, unsee_pre, subE_unsee, ha, hb, hau, hbu]
  | .code a b, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR, pre_prog, subE_prog, cl_subE σs η ρ₀ P d ρ hρ]
  | .tex κ b, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_substTs σs η ρ₀ b (s :: P) d ρ rb ws hρ
  | .unit, _, _, _, _, _, _ => by simp [substTs, VR]
  | .void, _, _, _, _, _, _ => by simp [substTs, VR]
  | .array _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .ptr _ _, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen, cl_subE σs η ρ₀ P d ρ hρ]
  | .ptrOpt _ _, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen, cl_subE σs η ρ₀ P d ρ hρ]
  | .loc _ _, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR, pre_sto, pre_tid, pre_pfr, pre_seen, pre_ini, pre_rini, subE_sto, subE_tid, subE_pfr, subE_seen, subE_ini, subE_rini, cl_subE σs η ρ₀ P d ρ hρ]
  | .share _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .cap _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .word _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .tok _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .word2 _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .tok2 _ _ _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .epair _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .tokE _ _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .mu b, P, d, ρ, rt, ws, hρ => by
      have e := cl_subE σs η ρ₀ P d ρ hρ (.mu b)
      simp only [substTs] at e
      simp only [substTs, VR, e]
      exact VR_substTs σs η ρ₀ b (_ :: P) d ρ rt ws hρ
  | .iall b, P, d, ρ, rt, ws, hρ => by
      simp only [substTs, VR]
      exact forall_congr' fun v =>
        VR_substTs σs η ρ₀ b P (d + 1) (vcons v ρ) rt ws (fun k => by rw [← Nat.add_assoc, vcons_succ]; exact hρ k)
  | .intS _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .int, _, _, _, _, _, _ => by simp [substTs, VR]
  | .tid, _, _, _, _, _, _ => by simp only [substTs, VR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen]
  | .fix _ _, _, _, _, _, _, _ => by simp [substTs, VR]
  | .lanes _ _, _, _, _, _, _, _ => by simp [substTs, VR]

/-- (T3c-5a) **`VR` at `μ` is `VR` at its unfolding**: the body with the bound
variable read as the closed `μ` type (its witness), whose relation is never
read since the variable is guarded (`Ty.wf` asks `unguarded 0 = false`). -/
theorem VR_unfold {η : TEnv} {ρ : Nat → Nat} {b : Ty} (hg : b.unguarded 0 = false) (rt : Shp)
    (ws : List Word) : VR ρ η (unfold1 (.mu b)) rt ws ↔ VR ρ η (.mu b) rt ws := by
  have e1 : unfold1 (.mu b) = substTs [.mu b] 0 0 b := substT_eq (.mu b) b 0 0
  rw [e1]
  refine (VR_substTs [.mu b] η ρ b [] 0 ρ rt ws (fun _ => rfl)).trans ?_
  have hr1 : ∀ k, k ≠ 0 →
      (TEnv.pre [] (subE ρ η [.mu b])).rels k = (η.push0 (cl ρ η.wit 0 0 (.mu b))).rels k := by
    intro k hk
    cases k with
    | zero => exact absurd rfl hk
    | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
  have hw1 : (TEnv.pre [] (subE ρ η [.mu b])).wit = (η.push0 (cl ρ η.wit 0 0 (.mu b))).wit := by
    funext k; cases k <;> simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
  simp only [VR]
  exact VR_relsG b 0 _ _ ρ rt ws hg hr1
    (fun k hk => by cases k with | zero => exact absurd rfl hk | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]) hw1 rfl

/-- **P1, pure operations.**  A step of a well-typed pure `let` keeps the frame
invariant, for some valuation extending the old one. -/
theorem pure_pres {K : TEnv → List Word → Prop} {p : Prog} {cx c' : Cx} {x : String} {op : Op} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env} {g : G} {s s' : St} {rt : Ty} {ws : List Word}
    (hT : OpT p cx x op c') (hA : PureOp op) (hi : FInv ρ η σs K cx env)
    (hr : (s', rt, ws) ∈ evalOp g env σs s op) (hw : ∀ k, Clo (η.wit k)) :
    ∃ ρ', FInv ρ' η σs K c' ((x, rt, ws) :: env) := by
  cases hT <;> simp only [PureOp, PackOK] at hA
  case atom a t c₁ hu hb =>
    obtain ⟨hi1, rt0, ws0, he, hiv, hs⟩ := use_FInv hu hi
    simp only [evalOp, he, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hb hi1 hiv hs⟩
  case pair =>
    rename_i hua hub hbd
    obtain ⟨hi1, rta, wa, hea, hva, hsa⟩ := use_FInv hua hi
    obtain ⟨hi2, rtb, wb, heb, hvb, hsb⟩ := use_FInv hub hi1
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    refine ⟨ρ, bind_FInv hbd hi2 ?_ ?_⟩
    · simp only [VR]
      refine ⟨shp rta, shp rtb, rfl, fun n hn => ?_⟩
      rw [shp_wc] at hn
      obtain ⟨us, hu, rfl⟩ := wc_some hn
      have hl := hsa.1 us hu
      rw [← hl]
      exact ⟨by simp, by simpa using hva, by simpa using hvb⟩
    · exact Lay_pair hsa hsb
  case addS a b t u i j ha hb hti htj hbd =>
    obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.2.1 ha hti
    obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp [VR, addW, hwa, hwb, ev]) (Lay_int _ rfl)⟩
  case addI a b t u o o' ha hb hti htj hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha hti
    obtain ⟨rb, wb, nb, heb, hwb⟩ := atom_int hi.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨na + nb, by simp [addW, hwa, hwb]⟩)
      (Lay_int _ rfl)⟩
  case subS a b t u i j d ha hb hti htj hent hbd =>
    obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.2.1 ha hti
    obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have e := hent ρ hi.1
    refine ⟨ρ, bind_FInv hbd hi ?_ (Lay_int _ rfl)⟩
    simp [VR, subW, hwa, hwb]; omega
  case nameI a j hj hbd =>
    obtain ⟨t, hpt, hti⟩ := hj
    obtain ⟨ra, wa, hea, hwa, hsa⟩ := atom_num hi.2.1 hpt hti
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hp := push_FInv x (ev ρ j) hi
    refine ⟨vcons (ev ρ j) ρ, bind_FInv hbd ⟨Sat_cons hp.1 ?_, hp.2⟩ ?_ (Lay_retype hti rfl hsa)⟩
    · rw [vcons_zero, ev_shift]
    · simp [VR, ev, vcons_zero, hwa]
  case rem a n ta o j v hta hio hj hjv hbd =>
    obtain ⟨tn, hpn, htn⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 hta hio
    obtain ⟨rn, wn, hen, hwn, -⟩ := atom_num hi.2.1 hpn htn
    have em : ev ρ j = ρ v + 1 := by simpa [ev] using hjv ρ hi.1
    simp only [evalOp, hea, hen, ol, numOf, hwa, hwn, em, Option.bind_eq_bind, Option.bind_some,
      pure, Nat.add_one_ne_zero, beq_iff_eq, ite_false, Option.toList_some,
      List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hk : na % (ρ v + 1) < ρ v + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    let k := na % (ρ v + 1)
    have h1 := push_FInv (x ++ "_d") (ρ v - k) hi
    have h2 := push_FInv x k h1
    refine ⟨vcons k (vcons (ρ v - k) ρ), bind_FInv hbd ⟨Sat_cons h2.1 ?_, h2.2⟩ ?_ (Lay_int _ rfl)⟩
    · simp only [ev, vcons_zero]
      rw [show v + 2 = (v + 1) + 1 from rfl, vcons_succ, vcons_succ,
        show (1 : Nat) = 0 + 1 from rfl, vcons_succ, vcons_zero]
      omega
    · simp [VR, ev, vcons_zero, k]
  case bits o a b ta tb oa ob ha hb hoa hob hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha hoa
    obtain ⟨rb, wb, nb, heb, hwb⟩ := atom_int hi.2.1 hb hob
    simp only [evalOp, hea, heb, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl)⟩
  case bit1 o a ta oa ha hoa hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha hoa
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl)⟩
  case vmatch lo hi' b t1 t2 t3 o1 o2 o3 h1 h2 h3 e1 e2 e3 hbd =>
    obtain ⟨r1, w1, n1, he1, hw1⟩ := atom_int hi.2.1 h1 e1
    obtain ⟨r2, w2, n2, he2, hw2⟩ := atom_int hi.2.1 h2 e2
    obtain ⟨r3, w3, n3, he3, hw3⟩ := atom_int hi.2.1 h3 e3
    simp only [evalOp, he1, he2, he3, ol, numOf, hw1, hw2, hw3, Option.bind_eq_bind, Option.bind_some,
      pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl)⟩
  case cvt sg w a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.2.1 ha hc
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _)⟩
  case toInt a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.2.1 ha (toIntSrc_cvt hc)
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl)⟩
  case asLanes sg w a ta ha hc hbd =>
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha ho
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl⟩ (Lay_lanes _ _ _ _)⟩
  case fop o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.2.1 hb hqb
    simp only [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _)⟩
  case fcmp o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.2.1 hb hqb
    simp only [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl)⟩
  case fop1 o a ta q ha hqa hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    simp only [evalOp, hea, fixOf, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    refine ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl, ?_⟩ (Lay_fix _ _ _ _)⟩
    cases o <;> exact fmask_lt _ _
  case lane a j ta tj q ha hqa hpj hl hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.2.1 hpj htj
    simp only [evalOp, hea, hej, lanesOf, ol, numOf, hwa, hwj, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _)⟩
  case setLane a j v ta tj tv q ha hqa hpj hl hv hqv hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.2.1 hpj htj
    obtain ⟨wv, nv, hev, hwv, -⟩ := atom_fix hi.2.1 hv hqv
    simp only [evalOp, hea, hej, hev, lanesOf, ol, numOf, hwa, hwj, hwv, Option.bind_eq_bind,
      Option.bind_some, pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bind_FInv hbd hi ⟨rfl, _, rfl⟩ (Lay_lanes _ _ _ _)⟩
  case band a m ta o j v hta hio hj hjv hbd =>
    obtain ⟨tm, hpm, htm⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 hta hio
    obtain ⟨rm, wm, hem, hwm, -⟩ := atom_num hi.2.1 hpm htm
    have em : ev ρ j = ρ v := by simpa [ev] using hjv ρ hi.1
    simp only [evalOp, hea, hem, ol, numOf, hwa, hwm, em, Option.bind_eq_bind, Option.bind_some,
      pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    let k := (na % W64) &&& ρ v
    have hk : k ≤ ρ v := Nat.and_le_right
    have h1 := push_FInv (x ++ "_d") (ρ v - k) hi
    have h2 := push_FInv x k h1
    refine ⟨vcons k (vcons (ρ v - k) ρ), bind_FInv hbd ⟨Sat_cons h2.1 ?_, h2.2⟩ ?_ (Lay_int _ rfl)⟩
    · simp only [ev, vcons_zero]
      rw [show v + 2 = (v + 1) + 1 from rfl, vcons_succ, vcons_succ,
        show (1 : Nat) = 0 + 1 from rfl, vcons_succ, vcons_zero]
      omega
    · simp [VR, ev, vcons_zero, k]
  case pack =>
    rename_i w body t hidx hwf hua hnl hsub hbd
    obtain ⟨hi1, rta, wa, hea, hva, hla⟩ := use_FInv hua hi
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have h1 := VR_sub hi1.1 hsub _ _ hva
    have h2 := (VR_instT _ η _ 0 ρ _ _).1 h1
    -- The source's shape is the package body's: skeletons absorb the witness.
    have es : shp rta = shp (substTs σs 0 1 body) := by
      rw [shp_of_eskel hla.2.1]
      unfold close
      rw [shp_sub hsub σs 0 0]
      exact shp_of_skel (skel_subst_instT σs [w] body 0 0 1 0)
    have ew : wc rta = wc (close σs (.iex body)) := by
      rw [← shp_wc, es, shp_wc]
      exact (wc_iex _).symm
    have v1 := Valid_of_eskel hla.2.1 hla.2.2.2.1
    unfold close at v1
    have v2 := Valid_sub hsub σs 0 0 _ v1
    have v3 := Valid_of_skel (skel_subst_instT σs [w] body 0 0 1 0) v2
    refine ⟨ρ, bind_FInv hbd hi1 ?_ ⟨ShapeC_wc ew hla.1, rfl, ew ▸ hla.2.2.1,
      by simpa only [close, substTs, Valid] using v3, rfl⟩⟩
    simp only [close, substTs, shp, VR]
    refine ⟨_, _, ev ρ w, rfl, ?_⟩
    rw [← es]
    simpa using h2
  case packT =>
    rename_i σ body t κ hg hwf had hua hnl hsub hbd
    obtain ⟨hi1, rta, wa, hea, hva, hla⟩ := use_FInv hua hi
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have h1 := VR_sub hi1.1 hsub _ _ hva
    -- T3c: the witness is `σ`'s closure; `σ`'s relation is not read (guarded)
    have e1 : Ty.substT 0 σ body = substTs [σ] 0 0 body := substT_eq σ body 0 0
    rw [e1] at h1
    have h3 := (VR_substTs [σ] η ρ body [] 0 ρ _ _ (fun _ => rfl)).1 h1
    have hr1 : ∀ k, k ≠ 0 → (TEnv.pre [] (subE ρ η [σ])).rels k = (η.push0 (cl ρ η.wit 0 0 σ)).rels k := by
      intro k hk
      cases k with
      | zero => exact absurd rfl hk
      | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
    have hw1 : (TEnv.pre [] (subE ρ η [σ])).wit = (η.push0 (cl ρ η.wit 0 0 σ)).wit := by
      funext k; cases k <;> simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
    have h2 := (VR_relsG body 0 _ (η.push0 (cl ρ η.wit 0 0 σ)) ρ _ _ (unguarded_of_guardT hg) hr1
      (fun k hk => by cases k with | zero => exact absurd rfl hk | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]) hw1 rfl).1 h3
    -- The witness sits under references only: signatures do not see it.
    have eσ := sig_pack σs body 0 0 σ hg
    have es : shp rta = shp (substTs σs 1 0 body) := by
      rw [shp_of_eskel hla.2.1]
      unfold close
      rw [shp_sub hsub σs 0 0]
      exact shp_of_sig eσ
    have ew : wc rta = wc (close σs (.tex κ body)) := by
      rw [← shp_wc, es, shp_wc]
      exact (wc_tex _ _).symm
    have v1 := Valid_of_eskel hla.2.1 hla.2.2.2.1
    unfold close at v1
    have v2 := Valid_sub hsub σs 0 0 _ v1
    have v3 := Valid_of_sig eσ v2
    refine ⟨ρ, bind_FInv hbd hi1 ?_ ⟨ShapeC_wc ew hla.1, rfl, ew ▸ hla.2.2.1,
      by simpa only [close, substTs, Valid] using v3, rfl⟩⟩
    simp only [close, substTs, shp, VR]
    refine ⟨_, _, cl ρ η.wit 0 0 σ, rfl, Clo_cl hw ρ σ,
      ⟨arrFree_cl hi.2.2.2.2.2.2.1.af σ 0 0 (admitsIn_arrFree had), fun hsh =>
        coupledOK_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.2.2.2.2.2.2.2.1 k hk) (admitsIn_share had hsh)
          (tb_of_wf σ (admitsIn_wf had)), fun hcp =>
        AffineCl.affine_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) σ
          ((admitsIn_word had).2 hcp) (tb_of_wf σ (admitsIn_wf had)), fun hno =>
        NoOwnCl.noOwn_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.2.2.2.2.2.2.2.2.2.1 k hk) σ
          (admitsIn_noOwn had hno) (tb_of_wf σ (admitsIn_wf had)), fun hsh =>
        rgnFree_cl0 ρ η.wit cx.ke (fun k hk => hi.2.2.2.2.2.2.2.2.2.2 k hk) (admitsIn_share had hsh)
          (hA.1 hsh), noIallV_cl hi.2.2.2.2.2.2.1.ni σ 0 0 hA.2,
        TermTv.mg_cl (fun k => (hw k).1) hi.2.2.2.2.2.2.1.mg σ 0 0 (mg_of_wf σ (admitsIn_wf had))⟩, ?_⟩
    rw [← es]
    exact h2

/-- **P4, pure operations.**  A well-typed pure `let` always has a step. -/
theorem pure_progress {K : TEnv → List Word → Prop} {p : Prog} {cx c' : Cx} {x : String} {op : Op} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env} (g : G) (s : St)
    (hT : OpT p cx x op c') (hA : PureOp op) (hi : FInv ρ η σs K cx env) :
    evalOp g env σs s op ≠ [] := by
  cases hT <;> simp only [PureOp, PackOK] at hA
  case atom a t c₁ hu hb =>
    obtain ⟨-, rt0, ws0, he, -⟩ := use_FInv hu hi
    simp [evalOp, he, ol]
  case pair =>
    rename_i hua hub hbd
    obtain ⟨hi1, rta, wa, hea, -⟩ := use_FInv hua hi
    obtain ⟨-, rtb, wb, heb, -⟩ := use_FInv hub hi1
    simp [evalOp, hea, heb, ol]
  case addS a b t u i j ha hb hti htj hbd =>
    obtain ⟨ra, wa, hea, -⟩ := atom_num hi.2.1 ha hti
    obtain ⟨rb, wb, heb, -⟩ := atom_num hi.2.1 hb htj
    simp [evalOp, hea, heb, ol]
  case addI a b t u o o' ha hb hti htj hbd =>
    obtain ⟨ra, wa, na, hea, -⟩ := atom_int hi.2.1 ha hti
    obtain ⟨rb, wb, nb, heb, -⟩ := atom_int hi.2.1 hb htj
    simp [evalOp, hea, heb, ol]
  case subS a b t u i j d ha hb hti htj hent hbd =>
    obtain ⟨ra, wa, hea, -⟩ := atom_num hi.2.1 ha hti
    obtain ⟨rb, wb, heb, -⟩ := atom_num hi.2.1 hb htj
    simp [evalOp, hea, heb, ol]
  case nameI a j hj hbd =>
    obtain ⟨t, hpt, hti⟩ := hj
    obtain ⟨ra, wa, hea, -⟩ := atom_num hi.2.1 hpt hti
    simp [evalOp, hea, ol]
  case rem a n ta o j v hta hio hj hjv hbd =>
    obtain ⟨tn, hpn, htn⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 hta hio
    obtain ⟨rn, wn, hen, hwn, -⟩ := atom_num hi.2.1 hpn htn
    have em : ev ρ j = ρ v + 1 := by simpa [ev] using hjv ρ hi.1
    simp [evalOp, hea, hen, ol, numOf, hwa, hwn, em]
  case bits o a b ta tb oa ob ha hb hoa hob hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha hoa
    obtain ⟨rb, wb, nb, heb, hwb⟩ := atom_int hi.2.1 hb hob
    simp [evalOp, hea, heb, ol, numOf, hwa, hwb]
  case bit1 o a ta oa ha hoa hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha hoa
    simp [evalOp, hea, ol, numOf, hwa]
  case vmatch lo hi' b t1 t2 t3 o1 o2 o3 h1 h2 h3 e1 e2 e3 hbd =>
    obtain ⟨r1, w1, n1, he1, hw1⟩ := atom_int hi.2.1 h1 e1
    obtain ⟨r2, w2, n2, he2, hw2⟩ := atom_int hi.2.1 h2 e2
    obtain ⟨r3, w3, n3, he3, hw3⟩ := atom_int hi.2.1 h3 e3
    simp [evalOp, he1, he2, he3, ol, numOf, hw1, hw2, hw3]
  case cvt sg w a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.2.1 ha hc
    simp [evalOp, hea, ol, numOf, hwa]
  case toInt a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.2.1 ha (toIntSrc_cvt hc)
    simp [evalOp, hea, ol, numOf, hwa]
  case asLanes sg w a ta ha hc hbd =>
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 ha ho
    simp [evalOp, hea, ol, numOf, hwa]
  case fop o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.2.1 hb hqb
    simp [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb]
  case fcmp o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.2.1 hb hqb
    simp [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb]
  case fop1 o a ta q ha hqa hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.2.1 ha hqa
    simp [evalOp, hea, fixOf, ol, numOf, hwa]
  case lane a j ta tj q ha hqa hpj hl hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.2.1 hpj htj
    simp [evalOp, hea, hej, lanesOf, ol, numOf, hwa, hwj]
  case setLane a j v ta tj tv q ha hqa hpj hl hv hqv hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.2.1 hpj htj
    obtain ⟨wv, nv, hev, hwv, -⟩ := atom_fix hi.2.1 hv hqv
    simp [evalOp, hea, hej, hev, lanesOf, ol, numOf, hwa, hwj, hwv]
  case band a m ta o j v hta hio hj hjv hbd =>
    obtain ⟨tm, hpm, htm⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.2.1 hta hio
    obtain ⟨rm, wm, hem, hwm, -⟩ := atom_num hi.2.1 hpm htm
    simp [evalOp, hea, hem, ol, numOf, hwa, hwm]
  case pack =>
    rename_i hidx hwf hua hnl hsub hbd
    obtain ⟨-, rta, wa, hea, -⟩ := use_FInv hua hi
    simp [evalOp, hea, ol]
  case packT =>
    rename_i hg hwf had hua hnl hsub hbd
    obtain ⟨-, rta, wa, hea, -⟩ := use_FInv hua hi
    simp [evalOp, hea, ol]

/-! ## §5 The branches: `ifeq`, `parity`, `split`, `unpack` -/

/-- `ifeq`'s false branch: the context `NoCx` builds is witnessed. -/
theorem noCx_pres {K : TEnv → List Word → Prop} {cx c' : Cx} {i j : Idx} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {env : Env}
    (hn : NoCx cx i j c') (hi : FInv ρ η σs K cx env) (hne : ev ρ i ≠ ev ρ j) :
    ∃ ρ', FInv ρ' η σs K c' env := by
  cases hn with
  | same => exact ⟨ρ, hi⟩
  | nzL h1 h2 =>
      rename_i u s
      have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1
      simp only [ev] at e1 e2
      have hu : 1 ≤ ρ u := by
        rcases Nat.eq_zero_or_pos (ρ u) with h | h
        · rw [h] at e1; simp at e1; omega
        · exact h
      have hp := push_FInv "_nz" (ρ u - 1) hi
      refine ⟨vcons (ρ u - 1) ρ, Sat_cons hp.1 ?_, hp.2⟩
      simp only [ev, vcons_succ, vcons_zero]; omega
  | nzR h1 h2 =>
      rename_i u s
      have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1
      simp only [ev] at e1 e2
      have hu : 1 ≤ ρ u := by
        rcases Nat.eq_zero_or_pos (ρ u) with h | h
        · rw [h] at e1; simp at e1; omega
        · exact h
      have hp := push_FInv "_nz" (ρ u - 1) hi
      refine ⟨vcons (ρ u - 1) ρ, Sat_cons hp.1 ?_, hp.2⟩
      simp only [ev, vcons_succ, vcons_zero]; omega

/-- **P1 + P4, `ifeq`.**  Both operands are one `num` word (so the machine steps),
and whichever branch it takes is well typed in a context the run witnesses. -/
theorem ifeq_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a b : At} {yes no : Expr} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env} (hT : Typed p cx (.ifeq a b yes no)) (hi : FInv ρ η σs K cx env) (htv : TvOK cx) :
    (∃ ra wa rb wb n m, evalAt env a = some (ra, [wa]) ∧ evalAt env b = some (rb, [wb]) ∧
      wa.val = .num n ∧ wb.val = .num m ∧
      (n = m → ∃ ρ' cy, Typed p cy yes ∧ TvOK cy ∧ skel cy.ret = skel cx.ret ∧ FInv ρ' η σs K cy env) ∧
      (n ≠ m → ∃ ρ' cn, Typed p cn no ∧ TvOK cn ∧ skel cn.ret = skel cx.ret ∧ FInv ρ' η σs K cn env)) ∨
    (∃ ra wa rb wb la lb, evalAt env a = some (ra, [wa]) ∧ evalAt env b = some (rb, [wb]) ∧
      wa.val = .loc ⟨la, 0⟩ 0 ∧ wb.val = .loc ⟨lb, 0⟩ 0 ∧ Typed p cx yes ∧ Typed p cx no) := by
  cases hT with
  | ifeqPlain hpe hy hn =>
      rcases atom_plainEq hi.2.1 hpe with ⟨⟨ra, wa, n, hea, hwa⟩, ⟨rb, wb, m, heb, hwb⟩⟩ |
          ⟨⟨ra, wa, la, hea, hwa⟩, ⟨rb, wb, lb, heb, hwb⟩⟩
      · exact Or.inl ⟨ra, wa, rb, wb, n, m, hea, heb, hwa, hwb, fun _ => ⟨ρ, cx, hy, htv, rfl, hi⟩,
          fun _ => ⟨ρ, cx, hn, htv, rfl, hi⟩⟩
      · exact Or.inr ⟨ra, wa, rb, wb, la, lb, hea, heb, hwa, hwb, hy, hn⟩
  | ifeq hia hib hy hnc hn =>
      rename_i c' i j
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun _ => ⟨ρ, cx, hy, htv, rfl, hi⟩, fun hne => ?_⟩
      obtain ⟨ρ', h'⟩ := noCx_pres hnc hi hne
      exact ⟨ρ', c', hn, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩
  | ifeqRec hia hib hrec hy hnc hn =>
      rename_i c' i j t v
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun heq => ?_, fun hne => ?_⟩
      · refine ⟨ρ, _, hy, htv, rfl, Sat_cons hi.1 ?_, hi.2⟩
        rcases hrec with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1; simp only [ev] at e1; omega
        · have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1; simp only [ev] at e1; omega
      · obtain ⟨ρ', h'⟩ := noCx_pres hnc hi hne
        exact ⟨ρ', c', hn, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩
  | ifeqZero hia hib hz hy hnc hn =>
      rename_i c' i j u s
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun heq => ?_, fun hne => ?_⟩
      · refine ⟨ρ, _, hy, htv, rfl, Sat_cons hi.1 ?_, hi.2⟩
        obtain ⟨hs, hz⟩ := hz
        simp only [ev]
        rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1; simp only [ev] at e1 e2
          rw [heq, e2] at e1
          exact (Nat.mul_eq_zero.1 e1.symm).resolve_left (by omega)
        · have e1 := h1 ρ hi.1; have e2 := h2 ρ hi.1; simp only [ev] at e1 e2
          rw [← heq, e2] at e1
          exact (Nat.mul_eq_zero.1 e1.symm).resolve_left (by omega)
      · obtain ⟨ρ', h'⟩ := noCx_pres hnc hi hne
        exact ⟨ρ', c', hn, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩

/-- **P1 + P4, `parity`.**  The operand is one `num` word, and the halving
facts of either branch are witnessed. -/
theorem parity_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {k : String} {ev₀ od : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.parity a k ev₀ od)) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) :
    ∃ r w n, evalAt env a = some (r, [w]) ∧ w.val = .num n ∧
      (n % 2 = 0 → ∃ ρ' c, Typed p c ev₀ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ' η σs K c env) ∧
      (n % 2 ≠ 0 → ∃ ρ' c, Typed p c od ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ' η σs K c env) := by
  cases hT with
  | parity hia hv he ho =>
      rename_i i v
      obtain ⟨ta, hpa, hta⟩ := hia
      obtain ⟨r, w, hea, hw, -⟩ := atom_num hi.2.1 hpa hta
      have e := hv ρ hi.1; simp only [ev] at e
      have hp := push_FInv k (ev ρ i / 2) hi
      refine ⟨r, w, _, hea, hw, fun h0 => ⟨_, _, he, push_TvOK k htv, skel_shiftI cx.ret 0, Sat_cons hp.1 ?_, hp.2⟩,
        fun h1 => ⟨_, _, ho, push_TvOK k htv, skel_shiftI cx.ret 0, Sat_cons hp.1 ?_, hp.2⟩⟩
      · simp only [ev, vcons_succ, vcons_zero]; omega
      · simp only [ev, vcons_succ, vcons_zero]; omega

/-- **P1 + P4, `split`.**  The operand is a runtime pair whose left component
has a layout (`Lay`), and both halves realise their static types. -/
theorem split_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {x y : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.split a x y e)) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) :
    ∃ ra rb ws us, evalAt env a = some (.prod ra rb, ws) ∧ accs ra = some us ∧
      ∃ c, Typed p c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ 
        FInv ρ η σs K c ((y, rb, ws.drop (nWords us)) :: (x, ra, ws.take (nWords us)) :: env) := by
  cases hT with
  | split hu hb1 hb2 he =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨ra, rb, rfl, hsa, hsb⟩ := eskel_eq_prod hs
      have hsh := hl.1
      have hwa : wc ra ≠ none := by
        intro h; apply hl.2.2.1; simp [wc_prod, h]
      have hwb : wc rb ≠ none := by
        intro h; apply hl.2.2.1; rw [wc_prod, h]; cases wc ra <;> rfl
      obtain ⟨us, hus⟩ : ∃ us, accs ra = some us := by
        cases h : accs ra with
        | none => exact absurd (by simp [wc, h]) hwa
        | some us => exact ⟨us, rfl⟩
      simp only [VR, shp, Shp.prod.injEq] at hv
      obtain ⟨sa, sb, ⟨rfl, rfl⟩, hf⟩ := hv
      refine ⟨ra, rb, ws, us, hea, hus, ?_⟩
      obtain ⟨hle, hva, hvb⟩ := hf (nWords us) (by rw [shp_wc]; simp [wc, hus])
      have sha : ShapeC ra (ws.take (nWords us)) := by
        intro us' h'; rw [hus] at h'; simp only [Option.some.injEq] at h'; subst h'
        simp; omega
      have shb : ShapeC rb (ws.drop (nWords us)) := by
        intro ub h'
        have := hsh (us ++ ub) (by simp [accs, hus, h'])
        rw [nWords_append] at this
        simp; omega
      have hvp := hl.2.2.2.1 (nWords us) (by simp [wc, hus])
      have hy := hl.2.2.2.2
      simp only [close, substTs, lyt, etok, Ty.prod.injEq] at hy
      exact ⟨_, he, split_TvOK hu hb1 hb2 htv, by rw [bind_ret hb2, bind_ret hb1, use_ret hu], bind_FInv hb2 (bind_FInv hb1 hi1 hva ⟨sha, hsa, hwa, hvp.1, hy.1⟩) hvb
        ⟨shb, hsb, hwb, hvp.2, hy.2⟩⟩

/-- **P1 + P4, `unpack`.**  The operand is a runtime package, and its witness
becomes the new index variable's value. -/
theorem unpack_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {i x : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.unpack a i x e)) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) :
    ∃ rb ws, evalAt env a = some (.iex rb, ws) ∧
      ∃ ρ' c, Typed p c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ' η σs K c ((x, rb, ws) :: env) := by
  cases hT with
  | unpack hu hb he =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨rb, rfl, hsb⟩ := eskel_eq_iex hs
      simp only [VR, shp, Shp.iex.injEq] at hv
      obtain ⟨n, sb, w, ⟨-, rfl⟩, hv⟩ := hv
      refine ⟨rb, ws, hea, vcons w ρ, _, he, unpack_TvOK hu hb htv, by rw [bind_ret hb, push_ret, skel_shiftI, use_ret hu],
        bind_FInv hb (push_FInv i w hi1) hv ⟨ShapeC_iex hl.1, ?_, ?_, ?_, ?_⟩⟩
      · rw [hsb]; exact congrArg etok (skel_subst_eq rfl σs 0 1 0)
      · rw [← wc_iex]; exact hl.2.2.1
      · exact hl.2.2.2.1
      · have hy := hl.2.2.2.2
        simp only [close, substTs, lyt, etok, Ty.iex.injEq] at hy
        show etok (lyt 0 rb) = etok (lyt 0 (substTs σs 0 0 _))
        congr 1
        rw [← lyt_down rb 1 0 (by omega), hy, lyt_down _ 1 0 (by omega),
          lyt_substTs _ σs 0 0 1 (by omega), lyt_substTs _ σs 0 0 0 (Nat.le_refl 0)]

/-- **P1 + P4, `unpackT`** (24e).  The operand is a runtime type package; the
body is bound at the runtime body with `Unit` for the erased witness.  T3c: the
new type variable is the package's (ghost) witness `s`, coherently (`consC`). -/
theorem unpackT_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {α x : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.unpackT a α x e)) (hi : FInv ρ η σs K cx env) (hc : Coh η)
    (htv : TvOK cx) :
    ∃ κ rb ws, evalAt env a = some (.tex κ rb, ws) ∧ ∃ s, Clo s ∧
      ∃ c, Typed p c e ∧ TvOK c ∧ skel (close (.unit :: σs) c.ret) = skel (close σs cx.ret) ∧
        FInv ρ (η.consC s) (.unit :: σs) K c ((x, Ty.substT 0 .unit rb, ws) :: env) := by
  cases hT with
  | unpackT hu hg hb he =>
      rename_i κ b
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨rb, rfl, hsb⟩ := eskel_eq_tex hs
      simp only [VR, shp, Shp.tex.injEq] at hv
      obtain ⟨n, sb, s, ⟨-, rfl⟩, hs, haf, hv⟩ := hv
      have hk : skel (Ty.substT 0 .unit rb) = skel (close (.unit :: σs) b) := by
        rw [skel_substT_unit, hsb]; unfold close; rw [skel_substTs, skel_substTs]
        exact substT_substS_unit _ _ 0
      have eσ : sig (Ty.substT 0 .unit rb) = sig rb := by
        have h1 : sig (Ty.substT 0 .unit rb) = sig (close (.unit :: σs) b) := by simp only [sig, hk]
        have h2 : sig rb = sig (substTs σs (0 + 1) 0 b) := by simp only [sig, hsb]
        rw [h1, h2]; unfold close; rw [← substTs_substT_unit]
        exact sig_pack σs b 0 0 .unit hg
      refine ⟨_, rb, ws, hea, s, hs, _, he, unpackT_TvOK hu hb htv,
        (by rw [bind_ret hb]; show skel (substTs (.unit :: σs) 0 0 (((_ : Ty)).shiftT 0)) = _
            rw [substTs_cons_shiftT, use_ret hu]; rfl), bind_FInv hb (pushT_FInv _ s hc hs haf hi1) ?_ ⟨?_, eskel_of_skel hk, ?_, ?_, ?_⟩⟩
      · rw [shp_of_sig eσ]
        refine (VR_relsG b 0 (η.push0 s) (η.consC s) ρ _ ws (unguarded_of_guardT hg) (fun k hk => ?_)
          (fun k hk => ?_) rfl rfl).1 hv
        all_goals (cases k with
          | zero => exact absurd rfl hk
          | succ k => simp [TEnv.push0, TEnv.ins, TEnv.consC, TEnv.insR])
      · exact ShapeC_wc (wc_of_sig eσ.symm) (ShapeC_wc (wc_tex _ rb) hl.1)
      · rw [wc_of_sig eσ, ← wc_tex _ rb]; exact hl.2.2.1
      · exact Valid_of_sig eσ.symm hl.2.2.2.1
      · have hy := hl.2.2.2.2
        simp only [close, substTs, lyt, etok, Ty.tex.injEq] at hy
        show etok (lyt 0 (Ty.substT 0 .unit rb)) = etok (lyt 0 (substTs (.unit :: σs) 0 0 b))
        congr 1
        rw [lyt_substT_unit, hy.2, ← lyt_substT_unit, substT_substTs_unit]

theorem eskel_eq_ptrOpt {rt : Ty} {μ : Mode} {u : Ty} (h : etok (skel rt) = .ptrOpt μ u) :
    ∃ μ' u', rt = .ptrOpt μ' u' ∧ skelM μ' = μ ∧ etok (skel u') = u := by
  cases rt with
  | ptrOpt μ' u' => simp only [skel, etok, Ty.ptrOpt.injEq] at h; exact ⟨μ', u', rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

theorem skel_eq_ptrOpt {rt : Ty} {μ : Mode} {u : Ty} (h : skel rt = .ptrOpt μ u) :
    ∃ μ' u', rt = .ptrOpt μ' u' ∧ skelM μ' = μ ∧ skel u' = u := by
  cases rt with
  | ptrOpt μ' u' => simp only [skel, Ty.ptrOpt.injEq] at h; exact ⟨μ', u', rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

/-- **P1 + P4, `ifnull`.**  The operand is one word at a runtime `Ptr?`: null,
or a pointer, which the second branch holds at runtime `Ptr`. -/
theorem ifnull_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {y : String} {e₁ e₂ : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.ifnull a e₁ y e₂)) (hi : FInv ρ η σs K cx env)
    (htv : TvOK cx) :
    ∃ μ u w, evalAt env a = some (.ptrOpt μ u, [w]) ∧
      ((w.val = .null ∧ ∃ c, Typed p c e₁ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ η σs K c env) ∨
       (∃ ad, w.val = .loc ad 0 ∧ ∃ c, Typed p c e₂ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ η σs K c ((y, .ptr μ u, [w]) :: env))) := by
  cases hT with
  | ifnull hu he1 hb he2 =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨μ', u', rfl, hμ, hsu⟩ := eskel_eq_ptrOpt hs
      simp only [VR] at hv
      rcases hv with hn | ⟨ad, cc, hp, hrest⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hn
        exact ⟨μ', u', w, hea, Or.inl ⟨hw, _, he1, (ifnull_TvOK hu hb htv).1, by rw [use_ret hu], hi1⟩⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hp
        refine ⟨μ', u', w, hea, Or.inr ⟨ad, hw, _, he2, (ifnull_TvOK hu hb htv).2, by rw [bind_ret hb, use_ret hu], bind_FInv hb hi1 ⟨ad, cc, by simp [hw], hrest⟩ ?_⟩⟩
        refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs], ⟨ad, by simp [hw]⟩, ?_⟩
        · show Ty.ptr (skelM μ') (etok (skel u')) = Ty.ptr _ _
          rw [hμ, hsu]
        · have hy := hl.2.2.2.2
          simp only [close, substTs, lyt, etok, Ty.ptrOpt.injEq] at hy
          simp only [close, substTs, lyt, etok, hy]

/-! ## §5b Sums: `inl`, `inr`, `case` (non-boxed) -/

/-! ### Seeing through wrappers -/

theorem tier_mu (t : Ty) : (Ty.mu t).tier = t.tier := by simp only [Ty.tier, info, top_cons]
theorem tier_tex (κ : Kind) (t : Ty) : (Ty.tex κ t).tier = t.tier := by simp only [Ty.tier, info, top_cons]
theorem tier_iall (t : Ty) : (Ty.iall t).tier = t.tier := by simp only [Ty.tier, info, top_shiftI]
theorem tier_iex (t : Ty) : (Ty.iex t).tier = t.tier := by simp only [Ty.tier, info, top_shiftI]
theorem tier_refine (t : Ty) (ψ : Pred) : (Ty.refine t ψ).tier = t.tier := by simp only [Ty.tier, info]

theorem asArm_congr {t t' : Ty} (hs : sumHead t = sumHead t') (ht : t.tier = t'.tier)
    (ha : armsOf t = armsOf t') : asArm t = asArm t' ∧ ofArm t = ofArm t' := by
  constructor
  · funext ws; simp only [asArm, hs, ht, ha]
  · funext j p; simp only [ofArm, hs, ht, ha]

theorem leaf_ptrs (w : Option Idx) : (Arms.leaf w).ptrs = 0 := by unfold Arms.leaf; split <;> rfl

theorem armK_ptr {a : Ty} (h : armK a = .ptr) : (info Ty.top a).arms = Arms.ptrArm := by
  unfold armK at h
  by_cases h1 : (info Ty.top a).arms = Arms.ptrArm
  · exact h1
  · simp only [h1, if_false] at h
    by_cases h2 : (info Ty.top a).arms = Arms.optArm
    · simp [h2] at h
    · simp only [h2, if_false] at h; split at h <;> simp at h

theorem armK_opt {a : Ty} (h : armK a = .opt) : (info Ty.top a).arms = Arms.optArm := by
  unfold armK at h
  by_cases h1 : (info Ty.top a).arms = Arms.ptrArm
  · simp [h1] at h
  · simp only [h1, if_false] at h
    by_cases h2 : (info Ty.top a).arms = Arms.optArm
    · exact h2
    · simp only [h2, if_false] at h; split at h <;> simp at h

/-- An atom's payload fits it when its words are valid and fill its width. -/
theorem atom_payok {a : Ty} {ws : List Word} {k : Nat} (hA : Atom a) (hv : Valid a ws)
    (hs : ShapeC a ws) (hk : a.rawWords = some k) : PayOK a ws := by
  have hw : wc a = some k := by
    simp only [Ty.rawWords, Ty.width] at hk
    cases h : (info Ty.top a).width with
    | none => simp [h] at hk
    | some w => simp only [h, Option.bind_some] at hk; exact wc_of_width h hk
  refine ⟨by rw [hk, ShapeC_len hs hw], fun h => ?_, fun h => ?_⟩
  · have e := armK_ptr h
    cases a <;> simp only [Atom] at hA
    case ptr =>
      simp only [Valid] at hv
      obtain ⟨ad, had⟩ := hv
      obtain ⟨w, rfl, hw⟩ := map_singleton had
      exact ⟨w, ad, rfl, hw⟩
    all_goals first
      | (have h' := congrArg Arms.ptrs e; simp [info, Info.leaf, leaf_ptrs, Arms.ptrArm] at h'; done)
      | (have h' := congrArg Arms.units e; simp [info, Arms.ptrArm, Arms.optArm] at h'; done)
  · have e := armK_opt h
    cases a <;> simp only [Atom] at hA
    case ptrOpt =>
      simp only [Valid] at hv
      rcases hv with hn | ⟨ad, had⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hn; exact ⟨w, rfl, Or.inl hw⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton had; exact ⟨w, rfl, Or.inr ⟨ad, hw⟩⟩
    case loc =>
      simp only [Valid] at hv
      rcases hv with hn | ⟨ad, had⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hn; exact ⟨w, rfl, Or.inl hw⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton had; exact ⟨w, rfl, Or.inr ⟨ad, hw⟩⟩
    all_goals first
      | (have h' := congrArg Arms.ptrs e; simp [info, Info.leaf, leaf_ptrs, Arms.optArm] at h'; done)
      | (have h' := congrArg Arms.units e; simp [info, Arms.ptrArm, Arms.optArm] at h'; done)

theorem asArm_atom {rt : Ty} {ws : List Word} (hA : Atom rt) (hv : Valid rt ws) (hs : ShapeC rt ws)
    (ht : rt.tier ≠ .boxed) (hsh : sumHead rt = false) (harms : armsOf rt = [rt]) :
    ∃ j p arm, asArm rt ws = some (j, p) ∧ (armsOf rt)[j]? = some arm ∧ PayOK arm p ∧
      ∃ q, ofArm rt j p = some q ∧ VEq q ws := by
  obtain ⟨⟨k, hk, -⟩, -⟩ := arm_of_tier (a := rt) ht (by rw [harms]; simp)
  exact ⟨0, ws, rt, by simp [asArm, hsh], by simp [harms], atom_payok hA hv hs hk, ws,
    by simp [ofArm, hsh], rfl⟩

/-- **The machine's `asArm` succeeds on valid words** at a non-boxed runtime type,
canonically, with a fitting payload. -/
theorem asArm_valid : ∀ (rt : Ty) (ws : List Word), Valid rt ws → ShapeC rt ws → rt.tier ≠ .boxed →
    ∃ j p arm, asArm rt ws = some (j, p) ∧ (armsOf rt)[j]? = some arm ∧ PayOK arm p ∧
      ∃ q, ofArm rt j p = some q ∧ VEq q ws := by
  intro rt
  induction rt with
  | sum a b _ _ =>
      intro ws hv _ ht
      rcases hv with hb | ⟨j, p, arm, hd, ha, hp, ⟨q, hq, eq⟩, -, -⟩
      · exact absurd hb ht
      exact ⟨j, p, arm, by simp only [asArm, sumHead, ite_true]; exact hd, ha, hp, q,
        by simp only [ofArm, sumHead, ite_true]; exact hq, eq⟩
  | void => intro ws hv; exact hv.elim
  | refine t ψ ih =>
      intro ws hv hs ht
      obtain ⟨e1, e2⟩ := asArm_congr (t := .refine t ψ) (t' := t) rfl (tier_refine t ψ) rfl
      rw [e1, e2]; exact ih ws hv (ShapeC_wc (by simp [wc, accs]) hs) (tier_refine t ψ ▸ ht)
  | mu t ih =>
      intro ws hv hs ht
      obtain ⟨e1, e2⟩ := asArm_congr (t := .mu t) (t' := t) rfl (tier_mu t) rfl
      rw [e1, e2]; exact ih ws hv (ShapeC_wc (by simp [wc, accs]) hs) (tier_mu t ▸ ht)
  | iall t ih =>
      intro ws hv hs ht
      obtain ⟨e1, e2⟩ := asArm_congr (t := .iall t) (t' := t) rfl (tier_iall t) rfl
      rw [e1, e2]; exact ih ws hv (ShapeC_wc (by simp [wc, accs]) hs) (tier_iall t ▸ ht)
  | iex t ih =>
      intro ws hv hs ht
      obtain ⟨e1, e2⟩ := asArm_congr (t := .iex t) (t' := t) rfl (tier_iex t) rfl
      rw [e1, e2]; exact ih ws hv (ShapeC_wc (wc_iex t) hs) (tier_iex t ▸ ht)
  | tex κ t ih =>
      intro ws hv hs ht
      obtain ⟨e1, e2⟩ := asArm_congr (t := .tex κ t) (t' := t) rfl (tier_tex κ t) rfl
      rw [e1, e2]; exact ih ws hv (ShapeC_wc (wc_tex κ t) hs) (tier_tex κ t ▸ ht)
  | _ => intro ws hv hs ht; exact asArm_atom (by trivial) hv hs ht rfl rfl

/-! ### Injection: the machine's result and its invariant -/

theorem shp_lnorm : ∀ t : Ty, shp (lnorm t) = shp t := by
  intro t
  induction t with
  | prod a b iha ihb => simp only [lnorm, shp, iha, ihb]
  | iex t ih =>
      have e := wc_lnorm (.iex t)
      simp only [lnorm] at e ⊢; simp only [shp, ih, e]
  | refine t ψ ih => simp only [lnorm, shp, ih]
  | sum a b _ _ =>
      show Shp.sum (wc (lnorm (.sum a b))) (lnorm (lnorm (.sum a b))) = _
      rw [wc_lnorm, lnorm_idem]; rfl
  | mu t ih => simp only [lnorm, shp, ih]
  | tex κ t ih => have e := wc_lnorm (.tex κ t); simp only [lnorm] at e ⊢; simp only [shp, e, ih]
  | iall t ih => simp only [lnorm, shp, ih]
  | word r P => have e := wc_lnorm (.word r P); simp only [lnorm] at e ⊢; simp only [shp, e]
  | _ => first | rfl | (simp [lnorm, shp, wc, accs, sig_idem]; done)

theorem encodeArm_len {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) : q.length = if tr = .wide then 2 else 1 := by
  cases tr with
  | boxed => simp [encodeArm] at h
  | wide =>
      simp only [encodeArm] at h
      split at h <;> simp at h <;> subst h <;> rfl
  | niche =>
      simp only [encodeArm] at h
      cases ha : as[j]? with
      | none => simp [ha, bind, Option.bind] at h
      | some arm =>
          simp only [ha, bind, Option.bind] at h
          split at h <;> (try split at h) <;> (try split at h) <;> simp at h <;> subst h <;> simp

/-- Decoding then re-encoding moves pointer words whole: equal values give
`WLe`. -/
theorem dec_enc_wle {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p q : List Word}
    (hd : decodeArm tr as ws = some (j, p)) (he : encodeArm tr as j p = some q) (e : VEq q ws) :
    WLe ws q := by
  cases tr with
  | boxed => simp [decodeArm] at hd
  | niche =>
    match ws, hd with
    | [w], hd =>
      have hq1 : q.length = 1 := by have := encodeArm_len he; simpa using this
      match q, hq1 with
      | [x], _ =>
        simp only [VEq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
        refine ⟨⟨e.symm, fun a g hw => ?_⟩, trivial⟩
        simp only [decodeArm, hw] at hd
        cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
        | none => simp [h1, bind, Option.bind] at hd
        | some pr =>
          simp [h1, bind, Option.bind, pure] at hd
          obtain ⟨rfl, rfl⟩ := hd
          simp only [encodeArm, bind, Option.bind] at he
          cases h2 : as[pr.1]? with
          | none => simp [h2] at he
          | some arm =>
            simp only [h2] at he
            cases hk : armK arm <;> simp [hk] at he <;> (subst he; exact Nat.le_refl _)
    | [], hd => simp [decodeArm] at hd
    | _ :: _ :: _, hd => simp [decodeArm] at hd
  | wide =>
    match ws, hd with
    | [t, w], hd =>
      have hq2 : q.length = 2 := by have := encodeArm_len he; simpa using this
      match q, hq2 with
      | [x0, x1], _ =>
        simp only [VEq, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
        cases ht : t.val with
        | num k =>
          simp only [decodeArm, ht] at hd
          cases h1 : as[k]? with
          | none => simp [h1, bind, Option.bind] at hd
          | some arm =>
            simp only [h1, bind, Option.bind] at hd
            refine ⟨⟨e.1.symm, fun a g h => by rw [ht] at h; cases h⟩, ⟨e.2.symm, fun a g hw => ?_⟩, trivial⟩
            by_cases hr : arm.rawWords = some 0
            · simp [hr, pure] at hd; obtain ⟨rfl, rfl⟩ := hd
              simp [encodeArm] at he
              obtain ⟨-, rfl⟩ := he
              rw [← e.2] at hw; simp at hw
            · simp [hr, pure] at hd; obtain ⟨rfl, rfl⟩ := hd
              simp [encodeArm] at he
              obtain ⟨-, rfl⟩ := he
              exact Nat.le_refl _
        | _ => simp [decodeArm, ht] at hd
    | [], hd => simp [decodeArm] at hd
    | [_], hd => simp [decodeArm] at hd
    | _ :: _ :: _ :: _, hd => simp [decodeArm] at hd

/-- A word list's own arm, re-encoded, carries its pointer views. -/
theorem asArm_ofArm_wle {rt : Ty} {ws : List Word} {j : Nat} {p q : List Word}
    (ha : asArm rt ws = some (j, p)) (ho : ofArm rt j p = some q) (e : VEq q ws) : WLe ws q := by
  unfold asArm at ha; unfold ofArm at ho
  split at ha
  · rename_i hs; rw [if_pos hs] at ho; exact dec_enc_wle ha ho e
  · rename_i hs; rw [if_neg hs] at ho; simp at ha; obtain ⟨rfl, rfl⟩ := ha; simp at ho; subst ho
    exact WLe_refl _

theorem shape_sum {a b : Ty} {j : Nat} {p q : List Word}
    (h : encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j p = some q) : ShapeC (.sum a b) q := by
  intro us hu
  rw [encodeArm_len h]
  simp only [accs] at hu
  split at hu <;> simp only [Option.some.injEq] at hu <;> subst hu <;> rename_i hw <;>
    simp [hw, nWords, Acc.size]

theorem wc_sum_ne (a b : Ty) : wc (.sum a b) ≠ none := by
  simp only [wc, accs]; split <;> simp

theorem skel_eq_sum {rt a b : Ty} (h : skel rt = .sum a b) :
    ∃ ra rb, rt = .sum ra rb ∧ skel ra = a ∧ skel rb = b := by
  cases rt with
  | sum ra rb => simp only [skel, Ty.sum.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, e] at h
  | _ => simp [skel] at h

theorem eskel_eq_sum {rt a b : Ty} (h : etok (skel rt) = .sum a b) :
    ∃ ra rb, rt = .sum ra rb ∧ etok (skel ra) = a ∧ etok (skel rb) = b := by
  cases rt with
  | sum ra rb => simp only [skel, etok, Ty.sum.injEq] at h; exact ⟨ra, rb, rfl, h.1, h.2⟩
  | refine t ψ => rcases rf_cases (skel t) with e | ⟨u, e⟩ <;> simp [skel, etok, e] at h
  | _ => simp [skel, etok] at h

/-- The machine re-encodes a fitting payload at a non-boxed sum, canonically. -/
theorem enc_canon {S arm : Ty} {k : Nat} {p q : List Word} (hS : S.tier ≠ .boxed)
    (ha : (armsOf S)[k]? = some arm) (hp : PayOK arm p) (he : encodeArm S.tier (armsOf S) k p = some q) :
    ∃ p', decodeArm S.tier (armsOf S) q = some (k, p') ∧ VEq p p' ∧ PayOK arm p' ∧
      ∃ q', encodeArm S.tier (armsOf S) k p' = some q' ∧ VEq q' q := by
  obtain ⟨p', hd, ep⟩ := roundtrip hS ha hp he
  obtain ⟨q', hq', eq⟩ := encodeArm_vals ep he
  exact ⟨p', hd, ep, PayOK_vals ep hp, q', hq', eq.symm⟩

/-- **`inl`, value level.** -/
theorem inl_value {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {t τ rt : Ty} {ws : List Word}
    (hv : VR ρ η t (shp rt) ws) (hl : Lay σs t rt ws)
    (hnb : (Ty.sum rt (close σs τ)).tier ≠ .boxed) :
    ∃ j p q, asArm rt ws = some (j, p) ∧ ofArm (.sum rt (close σs τ)) j p = some q ∧
      VR ρ η (.sum t τ) (shp (.sum rt (close σs τ))) q ∧
      Lay σs (.sum t τ) (.sum rt (close σs τ)) q := by
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  have hta := (tier_sum hnb).1
  obtain ⟨j, p, arm, has, harm, hp, q1, hq1, eq1⟩ := asArm_valid rt ws hval hshape hta
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  obtain ⟨q, hq⟩ := encode_ok hnb harmS hp
  obtain ⟨p', hd, ep, hp', q', hq', eq'⟩ := enc_canon hnb harmS hp hq
  obtain ⟨q0, hq0, e0⟩ := ofArm_vals ep hq1
  have e0' : WLe ws q0 := by
    obtain ⟨p'', hd'', ep''⟩ := roundtrip_wle hnb harmS hp hq
    rw [hd] at hd''; cases hd''
    obtain ⟨q0', hq0', e0''⟩ := ofArm_wle ep'' hq1
    rw [hq0] at hq0'; cases hq0'
    exact WLe_trans (asArm_ofArm_wle has hq1 eq1) e0''
  have hlen := ArmsLe.length (arms_lnorm rt)
  refine ⟨j, p, q, has, by simp only [ofArm, sumHead, ite_true]; exact hq, ?_, ?_⟩
  · refine ⟨_, _, _, rfl, Or.inr ⟨j, p', ?_, fun _ => ⟨q0, ofArm_lnorm hq0, ?_⟩, fun h => ?_⟩⟩
    · have := decodeArm_mono (arms_lnorm (.sum rt (close σs τ))) hd
      rw [← tier_lnorm (.sum rt (close σs τ))] at this; exact this
    · rw [shp_lnorm]; exact VR_up _ _ _ _ e0' hv
    · omega
  · refine ⟨shape_sum hq, ?_, wc_sum_ne _ _, ?_, by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
    · show Ty.sum (etok (skel rt)) (etok (skel (close σs τ))) = _
      rw [hsk]; rfl
    · exact Or.inr ⟨j, p', arm, hd, harmS, hp', ⟨q', hq', eq'⟩,
        fun _ => ⟨q0, hq0, ShapeC_vals e0'.vals hshape, hwc, Valid_vals _ _ _ e0'.vals hval⟩,
        fun h => absurd h (by omega)⟩

/-- **`inr`, value level.**  Arm `m + j`, `m` the left type's arm count. -/
theorem inr_value {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {t τ rt : Ty} {ws : List Word}
    (hv : VR ρ η t (shp rt) ws) (hl : Lay σs t rt ws)
    (hnb : (Ty.sum (close σs τ) rt).tier ≠ .boxed) :
    ∃ j p q, asArm rt ws = some (j, p) ∧
      ofArm (.sum (close σs τ) rt) ((armsOf (close σs τ)).length + j) p = some q ∧
      VR ρ η (.sum τ t) (shp (.sum (close σs τ) rt)) q ∧
      Lay σs (.sum τ t) (.sum (close σs τ) rt) q := by
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  have hta := (tier_sum hnb).2
  obtain ⟨j, p, arm, has, harm, hp, q1, hq1, eq1⟩ := asArm_valid rt ws hval hshape hta
  generalize hm : (armsOf (close σs τ)).length = m
  have harmS : (armsOf (.sum (close σs τ) rt))[m + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (by omega)]
    rw [hm, Nat.add_sub_cancel_left]; exact harm
  obtain ⟨q, hq⟩ := encode_ok hnb harmS hp
  obtain ⟨p', hd, ep, hp', q', hq', eq'⟩ := enc_canon hnb harmS hp hq
  obtain ⟨q0, hq0, e0⟩ := ofArm_vals ep hq1
  have e0' : WLe ws q0 := by
    obtain ⟨p'', hd'', ep''⟩ := roundtrip_wle hnb harmS hp hq
    rw [hd] at hd''; cases hd''
    obtain ⟨q0', hq0', e0''⟩ := ofArm_wle ep'' hq1
    rw [hq0] at hq0'; cases hq0'
    exact WLe_trans (asArm_ofArm_wle has hq1 eq1) e0''
  have hlen : (armsOf (lnorm (close σs τ))).length = m := by
    rw [← ArmsLe.length (arms_lnorm _)]; exact hm
  refine ⟨j, p, q, has, by simp only [ofArm, sumHead, ite_true]; exact hq, ?_, ?_⟩
  · refine ⟨_, _, _, rfl, Or.inr ⟨m + j, p', ?_, fun h => absurd h (by omega), fun _ => ⟨q0, ?_, ?_⟩⟩⟩
    · have := decodeArm_mono (arms_lnorm (.sum (close σs τ) rt)) hd
      rw [← tier_lnorm (.sum (close σs τ) rt)] at this; exact this
    · rw [hlen, Nat.add_sub_cancel_left]; exact ofArm_lnorm hq0
    · rw [shp_lnorm]; exact VR_up _ _ _ _ e0' hv
  · refine ⟨shape_sum hq, ?_, wc_sum_ne _ _, ?_, by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
    · show Ty.sum (etok (skel (close σs τ))) (etok (skel rt)) = _
      rw [hsk]; rfl
    · refine Or.inr ⟨m + j, p', arm, hd, harmS, hp', ⟨q', hq', eq'⟩, fun h => absurd h (by omega),
        fun _ => ⟨q0, ?_, ShapeC_vals e0'.vals hshape, hwc, Valid_vals _ _ _ e0'.vals hval⟩⟩
      rw [hm, Nat.add_sub_cancel_left]; exact hq0


/-! ### The machine at a non-boxed sum -/

theorem projM_nb {g : G} {s : St} {t : Ty} {ws : List Word} (ht : t.tier ≠ .boxed) :
    projM g s t ws = ol ((asArm t ws).map fun (j, p) => (s, j, p)) := by
  have : isBoxed t = false := by simp [isBoxed, ht]
  simp only [projM, this]; rfl

theorem injM_nb {g : G} {s : St} {t : Ty} {j : Nat} {p : List Word} (ht : t.tier ≠ .boxed) :
    injM g s t j p = ol ((ofArm t j p).map (s, ·)) := by
  have : isBoxed t = false := by simp [isBoxed, ht]
  simp only [injM, this]; rfl

theorem tier_of_skel {t u : Ty} (h : skel t = skel u) : t.tier = u.tier := by
  rw [← tier_skel t, h, tier_skel]

theorem tier_of_eskel {t u : Ty} (h : etok (skel t) = etok (skel u)) : t.tier = u.tier := by
  rw [← tier_skel t, ← tier_etok (skel t), h, tier_etok, tier_skel]

/-- **P1 + P4, `case`.**  The operand is a runtime non-boxed sum; its arm picks
the branch, and the re-encoded payload is valid at the branch's component. -/
theorem case_step {K : TEnv → List Word → Prop} {p : Prog} {cx : Cx} {a : At} {x y : String} {e₁ e₂ : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : Typed p cx (.case a x e₁ y e₂)) (hi : FInv ρ η σs K cx env)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close σs t).tier ≠ .boxed) (htv : TvOK cx) :
    ∃ ra rb ws j p', evalAt env a = some (.sum ra rb, ws) ∧ (Ty.sum ra rb).tier ≠ .boxed ∧
      asArm (.sum ra rb) ws = some (j, p') ∧
      (j < (armsOf ra).length → ∃ q, ofArm ra j p' = some q ∧
        ∃ c, Typed p c e₁ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ η σs K c ((x, ra, q) :: env)) ∧
      ((armsOf ra).length ≤ j → ∃ q, ofArm rb (j - (armsOf ra).length) p' = some q ∧
        ∃ c, Typed p c e₂ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInv ρ η σs K c ((y, rb, q) :: env)) := by
  cases hT with
  | case hu hb1 he1 hb2 he2 =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨ra, rb, rfl, hsa, hsb⟩ := eskel_eq_sum hs
      have hS : (Ty.sum ra rb).tier ≠ .boxed := by
        rw [tier_of_eskel hl.2.1]; exact hnb _ _ hu
      obtain ⟨-, -, -, hval, hly⟩ := hl
      simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
      rcases hval with hbx | ⟨j, p', arm, hd, -, -, -, hA, hB⟩
      · exact absurd hbx hS
      simp only [VR, shp] at hv
      obtain ⟨n, Ra, Rb, hR, hv⟩ := hv
      simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
      obtain ⟨-, rfl, rfl⟩ := hR
      have htl := tier_lnorm (.sum ra rb)
      simp only [lnorm] at htl
      rcases hv with hbx | ⟨j', p'', hd', hl1, hl2⟩
      · rw [htl] at hbx; exact absurd hbx.1 hS
      have hd2 := decodeArm_mono (arms_lnorm (.sum ra rb)) hd
      simp only [lnorm] at hd2
      rw [htl, hd2] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨e1, e2⟩ := hd'
      subst e1; subst e2
      have hlen := ArmsLe.length (arms_lnorm ra)
      refine ⟨ra, rb, ws, j, p', hea, hS, by simp only [asArm, sumHead, ite_true]; exact hd, ?_, ?_⟩
      · intro hj
        obtain ⟨q, hq, hsa', hwa, hva⟩ := hA hj
        obtain ⟨q'', hq'', hvq⟩ := hl1 (by omega)
        rw [ofArm_lnorm hq, Option.some.injEq] at hq''
        subst hq''
        rw [shp_lnorm] at hvq
        exact ⟨q, hq, _, he1, (case_TvOK hu hb1 hb2 htv).1, by rw [bind_ret hb1, use_ret hu], bind_FInv hb1 hi1 hvq ⟨hsa', hsa, hwa, hva, hly.1⟩⟩
      · intro hj
        obtain ⟨q, hq, hsb', hwb, hvb⟩ := hB hj
        obtain ⟨q'', hq'', hvq⟩ := hl2 (by omega)
        rw [← hlen, ofArm_lnorm hq, Option.some.injEq] at hq''
        subst hq''
        rw [shp_lnorm] at hvq
        exact ⟨q, hq, _, he2, (case_TvOK hu hb1 hb2 htv).2, by rw [bind_ret hb2, use_ret hu], bind_FInv hb2 hi1 hvq ⟨hsb', hsb, hwb, hvb, hly.2⟩⟩

/-! ## §6 At the thread: `tstep` -/

/-- A thread whose frame is well typed at `cx`, witnessed by `ρ` and `η`;
(T3c-4) `cx`'s types keep their type variables in scope (`TvOK`, TermTv). -/
def ThInv (p : Prog) (th : TTh) : Prop :=
  ∃ ρ η cx, EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧ FInv ρ η th.σs (Resume p th.stack) cx th.env

/-- `ThInv` with the thread-wide part of the frame's `η` named (T3c-4d):
`CE η = E` (Σ, program, thread).  The memory invariant (TermMem) reads only
`E`, so each step lemma says how `E` moves; the steps here keep it. -/
def ThInvE (p : Prog) (E : TEnv) (th : TTh) : Prop :=
  ∃ ρ η cx, CE η = E ∧ EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧
    FInv ρ η th.σs (Resume p th.stack) cx th.env ∧ RetPw th.σs th.stack cx.ret

theorem ThInvE.thInv {p : Prog} {E : TEnv} {th : TTh} (h : ThInvE p E th) : ThInv p th := by
  obtain ⟨ρ, η, cx, -, hE, hT, hv, hF, -⟩ := h
  exact ⟨ρ, η, cx, hE, hT, hv, hF⟩

/-! ### (P1) A plain value of an `∀`-free type carries resources -/

/-- (P1) Every variable's plain relation is carried by its resourceful one. -/
def RInv (η : TEnv) : Prop :=
  (∀ k S ws, η.rels k S ws → ∃ R, η.rrs k S ws R) ∧ ∀ k S ws, η.urels k S ws → ∃ R, η.urrs k S ws R

theorem RInv_unsee {η : TEnv} (h : RInv η) : RInv η.unsee := ⟨h.2, h.2⟩

theorem RInv_push0 {η : TEnv} (h : RInv η) (s : Ty) : RInv (η.push0 s) := by
  constructor
  · intro k S ws hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk ⊢; exact h.1 k S ws hk
  · intro k S ws hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk ⊢; exact h.2 k S ws hk

theorem RInv_CE (η : TEnv) : RInv (CE η) :=
  ⟨fun _ _ _ h => (h : False).elim, fun _ _ _ h => (h : False).elim⟩

/-- **(P1) `VR → ∃ VRR`** at an `∀`-free type (`noIallV`): one resource for
the value (an `∀` would need one for every index). -/
theorem VR_VRR : ∀ (t : Ty) {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word},
    noIallV t = true → RInv η → VR ρ η t rt ws → ∃ R, VRR ρ η t rt ws R := by
  intro t
  induction t with
  | iall b _ => intro ρ η rt ws hn; simp [noIallV] at hn
  | refine t ψ ih =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) hr h.1
      exact ⟨R, by simp only [VRR]; exact ⟨hR, h.2⟩⟩
  | iex b ih =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      obtain ⟨n, rb, w, e, h⟩ := h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) hr h
      exact ⟨R, by simp only [VRR]; exact ⟨n, rb, w, e, hR⟩⟩
  | prod a b iha ihb =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      simp only [noIallV, Bool.and_eq_true] at hn
      obtain ⟨ra, rb, e, h⟩ := h
      cases hw : ra.wc with
      | none =>
          refine ⟨.zero, ?_⟩
          simp only [VRR]
          refine ⟨ra, rb, e, .zero, .zero, ?_, ?_, ?_⟩
          · exact (Res.zero_add _).symm
          · intro _; trivial
          · intro n hn'; rw [hw] at hn'; cases hn'
      | some n =>
          obtain ⟨hl, h1, h2⟩ := h n hw
          obtain ⟨Ra, hRa⟩ := iha hn.1 hr h1
          obtain ⟨Rb, hRb⟩ := ihb hn.2 hr h2
          refine ⟨Ra + Rb, ?_⟩
          simp only [VRR]
          refine ⟨ra, rb, e, Ra, Rb, rfl, ?_, ?_⟩
          · intro h0; rw [hw] at h0; cases h0
          · intro n' hn'; rw [hw] at hn'; cases hn'; exact ⟨hl, hRa, hRb⟩
  | sum a b iha ihb =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      simp only [noIallV, Bool.and_eq_true] at hn
      obtain ⟨n, Ra, Rb, e, h | ⟨j, p, hd, h1, h2⟩⟩ := h
      · obtain ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6, hL, hR⟩ := h
        by_cases hj : B.tag - s < (armsOf Ra).length
        · obtain ⟨q1, q2⟩ := hL hj
          cases hb : isBoxed Ra with
          | true =>
              obtain ⟨R, hR'⟩ := iha hn.1 hr (q1 hb)
              refine ⟨R, ?_⟩
              simp only [VRR]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun _ => ⟨fun _ => hR', fun hb' => (by rw [hb] at hb'; cases hb')⟩,
                fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
          | false =>
              obtain ⟨q, d1, d2, d3, d4, d5⟩ := q2 hb
              obtain ⟨R, hR'⟩ := iha hn.1 (RInv_unsee hr) d5
              refine ⟨R, ?_⟩
              simp only [VRR]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun _ => ⟨fun hb' => (by rw [hb] at hb'; cases hb'), fun _ => ⟨q, d1, d2, d3, d4, hR'⟩⟩,
                fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
        · have hj2 : (armsOf Ra).length ≤ B.tag - s := Nat.not_lt.1 hj
          obtain ⟨q1, q2⟩ := hR hj2
          cases hb : isBoxed Rb with
          | true =>
              obtain ⟨R, hR'⟩ := ihb hn.2 hr (q1 hb)
              refine ⟨R, ?_⟩
              simp only [VRR]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun hj' => absurd hj' hj,
                fun _ => ⟨fun _ => hR', fun hb' => (by rw [hb] at hb'; cases hb')⟩⟩⟩
          | false =>
              obtain ⟨q, d1, d2, d3, d4, d5⟩ := q2 hb
              obtain ⟨R, hR'⟩ := ihb hn.2 (RInv_unsee hr) d5
              refine ⟨R, ?_⟩
              simp only [VRR]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun hj' => absurd hj' hj,
                fun _ => ⟨fun hb' => (by rw [hb] at hb'; cases hb'), fun _ => ⟨q, d1, d2, d3, d4, hR'⟩⟩⟩⟩
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, d1, d2⟩ := h1 hj
          obtain ⟨R, hR'⟩ := iha hn.1 hr d2
          refine ⟨R, ?_⟩
          simp only [VRR]
          exact ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun _ => ⟨q, d1, hR'⟩,
            fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
        · obtain ⟨q, d1, d2⟩ := h2 (Nat.not_lt.1 hj)
          obtain ⟨R, hR'⟩ := ihb hn.2 hr d2
          refine ⟨R, ?_⟩
          simp only [VRR]
          exact ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun hj' => absurd hj' hj, fun _ => ⟨q, d1, hR'⟩⟩⟩
  | tvar k =>
      intro ρ η rt ws _ hr h; simp only [VR] at h
      obtain ⟨ws', hw, h⟩ := h
      obtain ⟨R, hR⟩ := hr.1 k rt ws' h
      exact ⟨R, by simp only [VRR]; exact ⟨ws', hw, hR⟩⟩
  | tex κ b ih =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      obtain ⟨n, rb, s, e, hc, hk, h⟩ := h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) (RInv_push0 hr s) h
      exact ⟨R, by simp only [VRR]; exact ⟨n, rb, s, e, hc, hk, hR⟩⟩
  | mu b ih =>
      intro ρ η rt ws hn hr h; simp only [VR] at h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) (RInv_push0 hr _) h
      exact ⟨R, by simp only [VRR]; exact hR⟩
  | void => intro ρ η rt ws _ _ h; simp only [VR] at h
  | word r P =>
      intro ρ η rt ws _ _ h; simp only [VR] at h
      by_cases hw : WordHolds P (ws.map (·.val))
      · exact ⟨_, by simp only [VRR]; exact ⟨h, Or.inl ⟨hw, rfl⟩⟩⟩
      · exact ⟨_, by simp only [VRR]; exact ⟨h, Or.inr ⟨hw, rfl⟩⟩⟩
  | word2 r P =>
      intro ρ η rt ws _ _ h; simp only [VR] at h
      by_cases hw : Word2Holds P (ws.map (·.val))
      · exact ⟨_, by simp only [VRR]; exact ⟨h, Or.inl ⟨hw, rfl⟩⟩⟩
      · exact ⟨_, by simp only [VRR]; exact ⟨h, Or.inr ⟨hw, rfl⟩⟩⟩
  | intS | int | tid | fix | lanes | code | epair =>
      intro ρ η rt ws _ _ h; simp only [VR] at h; exact ⟨_, by simp only [VRR]; exact ⟨h, rfl⟩⟩
  | ptr | loc | ptrOpt =>
      intro ρ η rt ws _ _ h; simp only [VR] at h; exact ⟨_, by simp only [VRR]; exact ⟨h, rfl⟩⟩
  | unit | cap | tok | tok2 | tokE | share | array =>
      intro ρ η rt ws _ _ _; exact ⟨_, by simp only [VRR]; exact rfl⟩

/-- (P1) A coherent view with `∀`-free witnesses: every variable's plain
relation is carried by its resourceful one (through the witness, `VR_VRR`). -/
theorem RInv_of {η : TEnv} (hc : Coh η) (hr : CohR η) (hw : WitAF η) : RInv η := by
  refine ⟨fun k S ws h => ?_, fun k S ws h => ?_⟩
  · obtain ⟨R, hR⟩ := VR_VRR (η.wit k) (hw k).2.1 (RInv_CE η) (((hc k).2.1 (fun _ => 0) S ws).1 h)
    exact ⟨R, ((hr k).1 (fun _ => 0) S ws R).2 hR⟩
  · obtain ⟨R, hR⟩ := VR_VRR (η.wit k) (hw k).2.1 (RInv_CE η.unsee) (((hc k).2.2 (fun _ => 0) S ws).1 h)
    exact ⟨R, ((hr k).2 (fun _ => 0) S ws R).2 hR⟩

/-- (P1) The resourceful return clause gives the plain one at an `∀`-free
return type. -/
theorem RetOKR_RetOK {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty}
    {KR : TEnv → Nat → List Word → Res → Prop} {K : TEnv → List Word → Prop}
    (hn : noIallV ret = true) (hw : WitAF η) (hK : ∀ E rd ws R, KR E rd ws R → K E ws)
    (h : RetOKR ρ η σs ret KR) : RetOK ρ η σs ret K := by
  intro η' he ws hv hl
  have hw' : WitAF η' := fun k => by rw [he.2.1]; exact hw k
  obtain ⟨R, hR⟩ := VR_VRR ret hn (RInv_of he.1 he.2.2.2.2.2.2.2.2.2.2.1 hw') hv
  exact hK _ _ _ _ (h η' he ws R hR hl)

/-- (P1) The resourceful frame invariant gives the plain one. -/
theorem FInvR_FInv {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {KR : TEnv → Nat → List Word → Res → Prop}
    {K : TEnv → List Word → Prop} {cx : Cx} {env : Env} {Rf : Res}
    (hn : noIallV cx.ret = true) (hK : ∀ E rd ws R, KR E rd ws R → K E ws)
    (h : FInvR ρ η σs KR cx env Rf) : FInv ρ η σs K cx env :=
  ⟨h.1.1, h.1.2.1, RetOKR_RetOK hn h.1.2.2.2.2.2.2.1 hK h.2.1, h.1.2.2.2⟩

/-- (P1) The resourceful continuation gives the plain one, when every frame's
context keeps an `∀`-free return type (`hT`, `TvOK`). -/
theorem ResumeR_Resume {p : Prog} (hT : ∀ c : Cx, TvOK c → noIallV c.ret = true) :
    ∀ (st : List Frame) (Rs : Res) (E : TEnv) (rd : Nat) (ws : List Word) (R : Res),
      ResumeR p st Rs E rd ws R → Resume p st E ws
  | [], _, _, _, _, _, _ => trivial
  | _ :: rest, _, _, _, _, _, h => by
      obtain ⟨Rc, Rrest, -, ρ, η, c, hCE, -, hEO, hTy, hTv, hF, hpw⟩ := h
      exact ⟨ρ, η, c, hCE, hEO, hTy.1, hTv,
        FInvR_FInv (hT c hTv) (fun E rd ws R h => ResumeR_Resume hT rest Rrest E rd ws R h) hF, hpw⟩

/-- **(P1) The resourceful thread invariant gives the plain one.** -/
theorem ThInvRE.thInvE {p : Prog} {E : TEnv} {th : TTh} {Tot : Res}
    (h : ThInvRE p E th Tot) : ThInvE p E th := by
  have hT : ∀ c : Cx, TvOK c → noIallV c.ret = true := fun _ h => h.2.2.2.2.2.2.2
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hEO, hTy, hTv, hF, -, hpw⟩ := h
  exact ⟨ρ, η, cx, hCE, hEO, hTy.1, hTv,
    FInvR_FInv (hT cx hTv) (fun E rd ws R h => ResumeR_Resume hT th.stack Rs E rd ws R h) hF, hpw⟩

/-- **P1 + P4 at the thread, pure `let`.** -/
theorem tstep_pure {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) (hA : PureOp op) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      have hne := pure_progress g (stOf mem pairs th) hop hA hi
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        cases op <;> simp only [PureOp] at hA <;> simp [tstep, hterm]
      rw [key]
      refine ⟨by simpa using hne, ?_⟩
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
      obtain ⟨ρ', h'⟩ := pure_pres hop hA hi hm (fun k => (hE.2.1 k).1)
      exact ⟨ρ', η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, h', retPw_skel hPS hpw (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `ifeq`.** -/
theorem tstep_ifeq {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  rcases ifeq_step hT hi htv with ⟨ra, wa, rb, wb, n, m, hea, heb, hwa, hwb, hy, hn⟩ |
      ⟨ra, wa, rb, wb, la, lb, hea, heb, hwa, hwb, hy, hn⟩
  rotate_left
  · simp only [tstep, hterm, hea, heb, hwa, hwb]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    by_cases h : la = lb
    · exact ⟨ρ, η, cx, rfl, hE, by simpa [h] using hy, htv, hi, retPw_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0)⟩
    · exact ⟨ρ, η, cx, rfl, hE, by simpa [h] using hn, htv, hi, retPw_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0)⟩
  simp only [tstep, hterm, hea, heb, hwa, hwb]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  by_cases h : n = m
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hy h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hn h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `parity`.** -/
theorem tstep_parity {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {k : String} {ev₀ od : Expr}
    (hterm : th.term = .parity a k ev₀ od) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨r, w, n, hea, hw, he, ho⟩ := parity_step hT hi htv
  simp only [tstep, hterm, hea, hw]
  refine ⟨by simp, ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  by_cases h : n % 2 = 0
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := he h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := ho h
    exact ⟨ρ', η, c, rfl, hE, by simpa [h] using hc, hvc, hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `split`.** -/
theorem tstep_split {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, us, hea, hus, c, hc, hvc, hk, hf⟩ := split_step hT hi htv
  simp only [tstep, hterm, hea, hus]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `unpack`.** -/
theorem tstep_unpack {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨rb, ws, hea, ρ', c, hc, hvc, hk, hf⟩ := unpack_step hT hi htv
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ', η, c, rfl, hE, hc, hvc, by simpa using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `unpackT`** (24e). -/
theorem tstep_unpackT {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {α x : String} {e : Expr}
    (hterm : th.term = .unpackT a α x e) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨κ, rb, ws, hea, s, hs, c, hc, hvc, hk, hf⟩ := unpackT_step hT hi hE.2.1 htv
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η.consC s, c, rfl, ⟨hE.1, Coh_consC hE.2.1 hs, CohR_consC hE.2.2 hs⟩, hc, hvc, by simpa using hf, retPw_skel hPS hpw hk⟩

/-- **P1 + P4 at the thread, `ifnull`.** -/
theorem tstep_ifnull {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨μ, u, w, hea, h⟩ := ifnull_step hT hi htv
  rcases h with ⟨hw, c, hc, hvc, hk, hf⟩ | ⟨ad, hw, c, hc, hvc, hk, hf⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `inl`** (non-boxed result; boxed sums are T3c). -/
theorem tstep_inl {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inl _ hu hb =>
          obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
          have hS : (Ty.sum rt (close th.σs τ)).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inl_value hv hl hS
          have hta := (tier_sum hS).1
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInv hb hi1 hvr hlay, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `inr`.** -/
theorem tstep_inr {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inr _ hu hb =>
          obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
          have hS : (Ty.sum (close th.σs τ) rt).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inr_value hv hl hS
          have hta := (tier_sum hS).2
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInv hb hi1 hvr hlay, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `case`.** -/
theorem tstep_case {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, j, p', hea, hS, has, hA, hB⟩ := case_step hT hi hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  by_cases hj : j < (armsOf ra).length
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hA hj
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa [withS] using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hB (by omega)
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, rfl, hE, hc, hvc, by simpa [withS] using hf, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-! ## §7 Frames: `call`, `tail`, `ret` (T3b-2d) -/

/-! ### Substitution composition on skeletons -/

theorem substS_shiftT (A : List Ty) : ∀ (x : Ty) (c j : Nat), j ≤ c →
    substS A (c + 1) (x.shiftT j) = (substS A c x).shiftT j := by
  intro x
  induction x with
  | tvar k =>
      intro c j h
      by_cases hk : k ≥ j
      · simp only [Ty.shiftT, hk, ite_true, substS]
        by_cases hc : k < c
        · simp [show k + 1 < c + 1 by omega, hc, Ty.shiftT, hk]
        · simp only [show ¬ (k + 1 < c + 1) by omega, hc, ite_false, show k + 1 - (c + 1) = k - c by omega]
          cases hA : A[k - c]? with
          | some σ => simp only; rw [shiftT_shiftTN c j σ h]
          | none =>
              have : A.length ≤ k - c := by simpa using hA
              simp only [Ty.shiftT]; rw [if_pos (by omega)]; congr 1; omega
      · simp only [Ty.shiftT, hk, ite_false, substS]
        simp [show k < c + 1 by omega, show k < c by omega, Ty.shiftT, hk]
  | mu t ih => intro c j h; simp only [Ty.shiftT, substS]; rw [ih (c + 1) (j + 1) (by omega)]
  | tex κ t ih => intro c j h; simp only [Ty.shiftT, substS]; rw [ih (c + 1) (j + 1) (by omega)]
  | refine t ψ ih => intro c j h; simp only [Ty.shiftT, substS]; rw [ih c j h, shiftT_rf]
  | _ => intros; simp_all [Ty.shiftT, substS]

theorem substS_shiftTN (A : List Ty) : ∀ (c : Nat) (σ : Ty), substS A c (shiftTN c σ) = shiftTN c (substS A 0 σ) := by
  intro c
  induction c with
  | zero => intro σ; rfl
  | succ c ih =>
      intro σ
      show substS A (c + 1) (Ty.shiftT 0 (shiftTN c σ)) = Ty.shiftT 0 (shiftTN c (substS A 0 σ))
      rw [substS_shiftT A _ c 0 (Nat.zero_le _), ih]

/-- Free type variables below `n`. -/
def TvB : Nat → Ty → Prop
  | n, .tvar k => k < n
  | n, .prod a b => TvB n a ∧ TvB n b
  | n, .sum a b => TvB n a ∧ TvB n b
  | n, .code a b => TvB n a ∧ TvB n b
  | n, .array _ t => TvB n t
  | n, .ptr _ t => TvB n t
  | n, .ptrOpt _ t => TvB n t
  | n, .loc _ t => TvB n t
  | n, .iall t => TvB n t
  | n, .iex t => TvB n t
  | n, .refine t _ => TvB n t
  | n, .mu t => TvB (n + 1) t
  | n, .tex _ t => TvB (n + 1) t
  | _, _ => True

theorem TvB_rf {n : Nat} {t : Ty} (h : TvB n t) : TvB n (rf t) := by
  cases t <;> simp_all [rf, TvB]

theorem TvB_skel : ∀ (t : Ty) (nt ni : Nat), t.wf nt ni = true → TvB nt (skel t) := by
  intro t
  induction t with
  | refine t ψ ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact TvB_rf (ih nt ni h.2)
  | prod a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | sum a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | code a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | array _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | ptr _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | ptrOpt _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | loc _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | mu t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | tex _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | iall t ih => intro nt ni h; simp only [Ty.wf] at h; exact ih _ _ h
  | iex t ih => intro nt ni h; simp only [Ty.wf] at h; exact ih _ _ h
  | _ => intros; simp_all [Ty.wf, skel, TvB]

theorem substS_comp (A B : List Ty) : ∀ (v : Ty) (c : Nat), TvB (c + B.length) v →
    substS A c (substS B c v) = substS (B.map (substS A 0)) c v := by
  intro v
  induction v with
  | tvar k =>
      intro c h
      simp only [TvB] at h
      by_cases hk : k < c
      · simp [substS, hk]
      · simp only [substS, hk, ite_false]
        obtain ⟨σ, hσ⟩ : ∃ σ, B[k - c]? = some σ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        simp only [hσ, List.getElem?_map, Option.map_some]
        exact substS_shiftTN A c σ
  | mu t ih => intro c h; simp only [TvB] at h; simp only [substS]; rw [ih (c + 1) (by simpa [Nat.add_right_comm] using h)]
  | tex κ t ih => intro c h; simp only [TvB] at h; simp only [substS]; rw [ih (c + 1) (by simpa [Nat.add_right_comm] using h)]
  | refine t ψ ih => intro c h; simp only [TvB] at h; simp only [substS]; rw [substS_rf, ih c h]
  | _ => intros; simp_all [substS, TvB]

/-- **Skeletons of an instantiated signature** (row 18): closing the caller's
static instance at the caller's `σs` has the skeleton of closing the
declaration at the runtime type arguments `enter` computes. -/
theorem skel_call (σs ts : List Ty) (us : List Idx) (u : Ty) (hu : TvB ts.length (skel u)) :
    skel (close σs (substTs ts.reverse 0 0 (instT us 0 u))) = skel (close (ts.map (close σs)).reverse u) := by
  simp only [close, skel_substTs, skel_instT]
  rw [substS_comp _ _ _ 0 (by simpa using hu)]
  congr 1
  simp only [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, close, skel_substTs]

/-! ### Layout forms under index instantiation and call substitution -/

theorem ms_shiftN : ∀ (n : Nat) (u : Idx) (k : Nat), k < n → (shiftN n u).mentions k = false
  | 0, _, _, h => absurd h (by omega)
  | n + 1, u, k, h => by
      simp only [shiftN]
      rcases k with _ | k
      · exact ms_shift_self 0 _
      · rw [ms_shift_succ 0 k (by omega)]; exact ms_shiftN n u k (by omega)

theorem ms_instI (us : List Idx) (d k : Nat) (hk : k < d) : ∀ i : Idx, (instI us d i).mentions k = i.mentions k
  | .lit _ => rfl
  | .var k' => by
      by_cases h : k' < d
      · simp only [instI, h, ite_true]
      · simp only [instI, h, ite_false]
        cases hu : us[k' - d]? with
        | some u =>
            simp only; rw [ms_shiftN d u k hk]
            simp only [Idx.mentions]; simp; omega
        | none =>
            have : us.length ≤ k' - d := by simpa using hu
            simp only [Idx.mentions]
            rw [show (k' - us.length == k) = false by simp; omega, show (k' == k) = false by simp; omega]
  | .add i j => by simp only [instI, Idx.mentions, ms_instI us d k hk i, ms_instI us d k hk j]
  | .sub i j => by simp only [instI, Idx.mentions, ms_instI us d k hk i, ms_instI us d k hk j]
  | .smul _ i => by simp only [instI, Idx.mentions, ms_instI us d k hk i]

theorem pms_instI (us : List Idx) (d k : Nat) (hk : k < d) : ∀ ψ : Pred, (instP us d ψ).mentions k = ψ.mentions k
  | .tt => rfl
  | .le i j => by simp only [instP, Pred.mentions, ms_instI us d k hk]
  | .eq i j => by simp only [instP, Pred.mentions, ms_instI us d k hk]
  | .and p q => by simp only [instP, Pred.mentions, pms_instI us d k hk p, pms_instI us d k hk q]
  | .ini i => by simp only [instP, Pred.mentions, ms_instI us d k hk]

theorem idxC_instI (us : List Idx) (d : Nat) (i : Idx) : idxC d (instI us d i) = idxC d i :=
  ofMs_congr (fun k hk => ms_instI us d k hk i)

theorem modeC_instM (us : List Idx) (d : Nat) (μ : Mode) : modeC d (instM us d μ) = modeC d μ := by
  cases μ <;> simp [instM, modeC, idxC_instI]

/-- **Instantiating the free index variables at depth `d` leaves `lyt d` alone.** -/
theorem lyt_instT (us : List Idx) : ∀ (t : Ty) (d : Nat), lyt d (instT us d t) = lyt d t := by
  intro t
  induction t with
  | iall t ih => intro d; simp only [instT, lyt]; rw [ih (d + 1)]
  | iex t ih => intro d; simp only [instT, lyt]; rw [ih (d + 1)]
  | refine t ψ ih =>
      intro d
      have hm : ∀ k, k < d → (instP us d ψ).mentions k = ψ.mentions k := fun k hk => pms_instI us d k hk ψ
      simp only [instT, lyt, ih d, anyB_congr (m := fun k => (instP us d ψ).mentions k) hm,
        ofMs_congr (m := fun k => (instP us d ψ).mentions k) hm]
  | tok r st =>
      intro d
      cases st with
      | none => simp [instT, lyt, idxC_instI]
      | some p => obtain ⟨P, i⟩ := p; simp [instT, lyt, idxC_instI]
  | _ => intro d; simp_all [instT, lyt, idxC_instI, modeC_instM]

/-- Index-closed: no index shift moves it. -/
def ICl (σ : Ty) : Prop := ∀ k, σ.shiftI k = σ

theorem shiftI_shiftT' : ∀ (t : Ty) (c k : Nat), (t.shiftT c).shiftI k = (t.shiftI k).shiftT c := by
  intro t
  induction t with
  | tvar j => intro c k; simp only [Ty.shiftT]; split <;> simp [Ty.shiftI, Ty.shiftT, *]
  | _ => intro c k; simp_all [Ty.shiftT, Ty.shiftI]

theorem ICl_shiftT {σ : Ty} (h : ICl σ) (j : Nat) : ICl (σ.shiftT j) := fun k => by rw [shiftI_shiftT', h k]

theorem ICl_shiftTN {σ : Ty} (h : ICl σ) : ∀ n, ICl (shiftTN n σ)
  | 0 => h
  | n + 1 => ICl_shiftT (ICl_shiftTN h n) 0

theorem shiftIN_ICl {x : Ty} (h : ICl x) : ∀ d, shiftIN d x = x
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, shiftIN_ICl h d, h 0]

theorem ICl_lyt0 (σ : Ty) : ICl (lyt 0 σ) := fun k => lyt_shiftI_id σ 0 k (Nat.zero_le k)

theorem shiftT_shiftIN' (X : Ty) (c : Nat) : ∀ d, (shiftIN d X).shiftT c = shiftIN d (X.shiftT c)
  | 0 => rfl
  | d + 1 => by simp only [shiftIN]; rw [← shiftI_shiftT', shiftT_shiftIN' X c d]

theorem substTs_shiftT_d (A : List Ty) : ∀ (x : Ty) (c j d : Nat), j ≤ c →
    substTs A (c + 1) d (x.shiftT j) = (substTs A c d x).shiftT j := by
  intro x
  induction x with
  | tvar k =>
      intro c j d h
      by_cases hk : k ≥ j
      · simp only [Ty.shiftT, hk, ite_true, substTs]
        by_cases hc : k < c
        · simp [show k + 1 < c + 1 by omega, hc, Ty.shiftT, hk]
        · simp only [show ¬ (k + 1 < c + 1) by omega, hc, ite_false, show k + 1 - (c + 1) = k - c by omega]
          cases hA : A[k - c]? with
          | some σ => simp only; rw [shiftT_shiftIN', shiftT_shiftTN c j σ h]
          | none =>
              have : A.length ≤ k - c := by simpa using hA
              simp only [Ty.shiftT]; rw [if_pos (by omega)]; congr 1; omega
      · simp only [Ty.shiftT, hk, ite_false, substTs]
        simp [show k < c + 1 by omega, show k < c by omega, Ty.shiftT, hk]
  | mu t ih => intro c j d h; simp only [Ty.shiftT, substTs]; rw [ih (c + 1) (j + 1) d (by omega)]
  | tex κ t ih => intro c j d h; simp only [Ty.shiftT, substTs]; rw [ih (c + 1) (j + 1) d (by omega)]
  | iall t ih => intro c j d h; simp only [Ty.shiftT, substTs]; rw [ih c j (d + 1) h]
  | iex t ih => intro c j d h; simp only [Ty.shiftT, substTs]; rw [ih c j (d + 1) h]
  | _ => intros; simp_all [Ty.shiftT, substTs]

theorem substTs_shiftTN_d (A : List Ty) (d : Nat) : ∀ (c : Nat) (σ : Ty),
    substTs A c d (shiftTN c σ) = shiftTN c (substTs A 0 d σ) := by
  intro c
  induction c with
  | zero => intro σ; rfl
  | succ c ih =>
      intro σ
      show substTs A (c + 1) d (Ty.shiftT 0 (shiftTN c σ)) = Ty.shiftT 0 (shiftTN c (substTs A 0 d σ))
      rw [substTs_shiftT_d A _ c 0 d (Nat.zero_le _), ih]

theorem substTs_depth {A : List Ty} (hA : ∀ σ ∈ A, ICl σ) : ∀ (Y : Ty) (c d : Nat),
    substTs A c d Y = substTs A c 0 Y := by
  intro Y
  induction Y with
  | tvar k =>
      intro c d
      simp only [substTs]
      split
      · rfl
      · cases h : A[k - c]? with
        | none => rfl
        | some σ =>
            simp only
            have hc := ICl_shiftTN (hA σ (List.mem_of_getElem? h)) c
            rw [shiftIN_ICl hc, shiftIN_ICl hc]
  | iall t ih => intro c d; simp only [substTs]; rw [ih c (d + 1), ih c 1]
  | iex t ih => intro c d; simp only [substTs]; rw [ih c (d + 1), ih c 1]
  | _ => intros; simp_all [substTs]

theorem substTs_shiftI_IC {A : List Ty} (hA : ∀ σ ∈ A, ICl σ) : ∀ (β : Ty) (c d k : Nat),
    (substTs A c d β).shiftI k = substTs A c d (β.shiftI k) := by
  intro β
  induction β with
  | tvar j =>
      intro c d k
      simp only [substTs, Ty.shiftI]
      split
      · rfl
      · cases h : A[j - c]? with
        | none => rfl
        | some σ =>
            simp only
            have hc := ICl_shiftTN (hA σ (List.mem_of_getElem? h)) c
            rw [shiftIN_ICl hc, hc k]
  | iall t ih => intro c d k; simp only [substTs, Ty.shiftI]; rw [ih c (d + 1) (k + 1)]
  | iex t ih => intro c d k; simp only [substTs, Ty.shiftI]; rw [ih c (d + 1) (k + 1)]
  | tok r st => intro c d k; simp [substTs, Ty.shiftI]
  | _ => intros; simp_all [substTs, Ty.shiftI]

theorem ICl_substTs {A : List Ty} (hA : ∀ σ ∈ A, ICl σ) {β : Ty} (hβ : ICl β) (c d : Nat) :
    ICl (substTs A c d β) := fun k => by rw [substTs_shiftI_IC hA, hβ k]

theorem TvB_lyt : ∀ (t : Ty) (n d : Nat), TvB n t → TvB n (lyt d t) := by
  intro t
  induction t with
  | refine t ψ ih =>
      intro n d h; simp only [TvB] at h; simp only [lyt]
      split
      · exact ih n d h
      · exact ih n d h
  | iall t ih => intro n d h; exact ih n (d + 1) h
  | iex t ih => intro n d h; exact ih n (d + 1) h
  | tok r st => intro n d h; simp [lyt, TvB]
  | _ => intro n d h; simp_all [lyt, TvB]

theorem TvB_of_wf : ∀ (t : Ty) (nt ni : Nat), t.wf nt ni = true → TvB nt t := by
  intro t
  induction t with
  | refine t ψ ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih nt ni h.2
  | prod a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | sum a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | code a b iha ihb => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ⟨iha _ _ h.1, ihb _ _ h.2⟩
  | array _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | ptr _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | ptrOpt _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | loc _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | mu t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | tex _ t ih => intro nt ni h; simp only [Ty.wf, Bool.and_eq_true] at h; exact ih _ _ h.2
  | iall t ih => intro nt ni h; simp only [Ty.wf] at h; exact ih _ _ h
  | iex t ih => intro nt ni h; simp only [Ty.wf] at h; exact ih _ _ h
  | _ => intros; simp_all [Ty.wf, TvB]

theorem substTs_TvB (σs : List Ty) : ∀ (v : Ty) (c d : Nat), TvB c v → substTs σs c d v = v := by
  intro v
  induction v with
  | tvar k => intro c d h; simp only [TvB] at h; simp [substTs, h]
  | mu t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih (c + 1) d h]
  | tex κ t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih (c + 1) d h]
  | iall t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih c (d + 1) h]
  | iex t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih c (d + 1) h]
  | _ => intros; simp_all [substTs, TvB]

/-- **Composition of index-closed substitutions.** -/
theorem substTs_comp_IC {A B : List Ty} (hA : ∀ σ ∈ A, ICl σ) (hB : ∀ σ ∈ B, ICl σ) :
    ∀ (Y : Ty) (c d : Nat), TvB (c + B.length) Y →
      substTs A c d (substTs B c d Y) = substTs (B.map (substTs A 0 0)) c d Y := by
  intro Y
  induction Y with
  | tvar k =>
      intro c d h
      simp only [TvB] at h
      by_cases hk : k < c
      · simp [substTs, hk]
      · simp only [substTs, hk, ite_false]
        obtain ⟨β, hβ⟩ : ∃ β, B[k - c]? = some β := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        simp only [hβ, List.getElem?_map, Option.map_some]
        have hb := hB β (List.mem_of_getElem? hβ)
        rw [shiftIN_ICl (ICl_shiftTN hb c), substTs_shiftTN_d,
          shiftIN_ICl (ICl_shiftTN (ICl_substTs hA hb 0 0) c), substTs_depth hA β 0 d]
  | mu t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih (c + 1) d (by simpa [Nat.add_right_comm] using h)]
  | tex κ t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih (c + 1) d (by simpa [Nat.add_right_comm] using h)]
  | iall t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih c (d + 1) h]
  | iex t ih => intro c d h; simp only [TvB] at h; simp only [substTs]; rw [ih c (d + 1) h]
  | _ => intros; simp_all [substTs, TvB]

/-- **Layout forms of an instantiated signature** (the `lyt` analogue of
`skel_call`). -/
theorem lyt_call (σs ts : List Ty) (us : List Idx) (u : Ty) (hu : TvB ts.length u) :
    lyt 0 (close σs (substTs ts.reverse 0 0 (instT us 0 u))) = lyt 0 (close (ts.map (close σs)).reverse u) := by
  rw [lyt_close, lyt_close]
  unfold close
  rw [lyt_substTs _ _ 0 0 0 (Nat.le_refl 0), lyt_instT,
    substTs_comp_IC (fun σ h => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 h; exact ICl_lyt0 x)
      (fun σ h => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 h; exact ICl_lyt0 x) _ 0 0
      (by simpa using TvB_lyt u _ 0 hu)]
  congr 1
  simp only [List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  exact (lyt_close σs t).symm


/-! ### Row 18: `VR` under a call's instantiation -/

/-- `ρ` with the values `vs` inserted at `d` (a call's index arguments). -/
def vinsL (d : Nat) (vs : List Nat) (ρ : Nat → Nat) : Nat → Nat :=
  fun k => if k < d then ρ k else match vs[k - d]? with
    | some v => v
    | none => ρ (k - vs.length)

theorem vinsL_succ (d : Nat) (vs : List Nat) (v : Nat) (ρ : Nat → Nat) :
    vinsL (d + 1) vs (vcons v ρ) = vcons v (vinsL d vs ρ) := by
  funext k
  cases k with
  | zero => simp [vinsL, vins]
  | succ k =>
      rw [vcons_succ]
      simp only [vinsL, show k + 1 - (d + 1) = k - d by omega]
      by_cases h : k < d
      · simp [h, vcons_succ]
      · simp only [show ¬ (k + 1 < d + 1) by omega, h, ite_false]
        cases hv : vs[k - d]? with
        | some x => rfl
        | none =>
            have : vs.length ≤ k - d := by simpa using hv
            simp only
            rw [show k + 1 - vs.length = (k - vs.length) + 1 by omega, vcons_succ]

theorem ev_instIs (us : List Idx) (d : Nat) (ρ : Nat → Nat) :
    ∀ i : Idx, ev ρ (instI us d i) = ev (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) i
  | .lit n => by simp [instI, ev]
  | .var k => by
      simp only [instI]
      by_cases h1 : k < d
      · simp [h1, ev, vinsL]
      · simp only [h1, ite_false]
        cases hu : us[k - d]? with
        | some u => simp [ev, vinsL, h1, hu, ev_shiftN]
        | none =>
            have : us.length ≤ k - d := by simpa using hu
            simp [ev, vinsL, h1, hu]
  | .add i j => by simp [instI, ev, ev_instIs us d ρ i, ev_instIs us d ρ j]
  | .sub i j => by simp [instI, ev, ev_instIs us d ρ i, ev_instIs us d ρ j]
  | .smul n i => by simp [instI, ev, ev_instIs us d ρ i]

theorem cl_instTs (us : List Idx) (d : Nat) (ρ : Nat → Nat) (W : Nat → Ty) (t : Ty) :
    cl ρ W 0 0 (instT us d t) = cl (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) W 0 0 t :=
  cl_instT (us := us) (d0 := d) (ρ := ρ) (ρ' := vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ)
    (fun k hk => by simp [vinsL, hk])
    (fun j u hj => by
      have h1 : ¬ d + j < d := by omega
      simp [vinsL, h1, hj])
    (fun k => by
      have h1 : ¬ (d + us.length + k < d) := by omega
      have h2 : (us.map (ev (fun k => ρ (k + d))))[d + us.length + k - d]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp only [vinsL, h1, if_false, h2, List.length_map]
      congr 1; omega) W t 0 0

theorem IniR_insts (us : List Idx) (d : Nat) (ρ : Nat → Nat) (ini : WeakMem.AllocLabel → Nat) (ws : List Word) :
    ∀ ψ : Pred, IniR ρ ini (instP us d ψ) ws ↔
      IniR (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) ini ψ ws := by
  intro ψ
  induction ψ with
  | ini k => simp only [instP, IniR, ev_instIs]
  | and p q ihp ihq => simp only [instP, IniR, ihp, ihq]
  | _ => simp [instP, IniR]

theorem VR_instTs (us : List Idx) (η : TEnv) :
    ∀ (t : Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word),
      VR ρ η (instT us d t) rt ws ↔ VR (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) η t rt ws
  | .intS i, d, ρ, _, _ => by simp [instT, VR, ev_instIs]
  | .int, _, _, _, _ => by simp [instT, VR]
  | .tid, _, _, _, _ => by simp [instT, VR]
  | .fix _ _, _, _, _, _ => by simp [instT, VR]
  | .lanes _ _, _, _, _, _ => by simp [instT, VR]
  | .refine t ψ, d, ρ, rt, ws => by
      simp only [instT, VR]; exact and_congr (VR_instTs us η t d ρ rt ws) (by rw [TEnv.selIni_instT]; exact IniR_insts us d ρ _ ws ψ)
  | .iex b, d, ρ, rt, ws => by
      have e : ∀ v, vinsL (d + 1) (us.map (ev (fun k => vcons v ρ (k + (d + 1))))) (vcons v ρ) =
          vcons v (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vinsL_succ]
      simp only [instT, VR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      rw [VR_instTs us η b (d + 1) (vcons v ρ) rb ws, e v]
  | .prod a b, d, ρ, rt, ws => by
      simp only [instT, VR, VR_instTs us η a d ρ, VR_instTs us η b d ρ]
  | .unit, _, _, _, _ => by simp [instT, VR]
  | .void, _, _, _, _ => by simp [instT, VR]
  | .sum a b, d, ρ, rt, ws => by
      simp only [instT, VR, VR_instTs us η a d ρ, VR_instTs us η b d ρ, VR_instTs us η.unsee a d ρ,
        VR_instTs us η.unsee b d ρ]
  | .code a b, d, ρ, rt, ws => by
      simp only [instT, VR, cl_instTs]
  | .array _ _, _, _, _, _ => by simp [instT, VR]
  | .ptr _ _, _, _, _, _ => by simp only [instT, VR, cl_instTs, ModeOK_inst]
  | .ptrOpt _ _, _, _, _, _ => by simp only [instT, VR, cl_instTs, ModeOK_inst]
  | .loc _ _, _, _, _, _ => by simp only [instT, VR, cl_instTs, ModeOK_inst, modeIni_inst, modeIni_inst]
  | .share _, _, _, _, _ => by simp [instT, VR]
  | .cap _ _, _, _, _, _ => by simp [instT, VR]
  | .word _ _, _, _, _, _ => by simp [instT, VR]
  | .tok _ _, _, _, _, _ => by simp [instT, VR]
  | .word2 _ _, _, _, _, _ => by simp [instT, VR]
  | .tok2 _ _ _ _, _, _, _, _ => by simp [instT, VR]
  | .epair _ _, _, _, _, _ => by simp [instT, VR]
  | .tokE _ _ _, _, _, _, _ => by simp [instT, VR]
  | .tvar _, _, _, _, _ => by simp [instT, VR]
  | .mu b, d, ρ, rt, ws => by
      have e := cl_instTs us d ρ η.wit (.mu b)
      simp only [instT] at e
      simp only [instT, VR, e]
      exact VR_instTs us _ b d ρ rt ws
  | .iall b, d, ρ, rt, ws => by
      have e : ∀ v, vinsL (d + 1) (us.map (ev (fun k => vcons v ρ (k + (d + 1))))) (vcons v ρ) =
          vcons v (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vinsL_succ]
      simp only [instT, VR]
      refine forall_congr' fun v => ?_
      rw [VR_instTs us η b (d + 1) (vcons v ρ) rt ws, e v]
  | .tex κ b, d, ρ, rt, ws => by
      simp only [instT, VR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VR_instTs us (η.push0 s) b d ρ rb ws

/-- **Row 18, the call lemma**: `VR` at the caller's static instance of a
signature type is `VR` at the declared type, in the callee's `ρ` and `η`. -/
theorem VR_call (ts : List Ty) (us : List Idx) (η : TEnv) (ρ : Nat → Nat) (u : Ty) (rt : Shp) (ws : List Word) :
    VR ρ η (substTs ts.reverse 0 0 (instT us 0 u)) rt ws ↔
      VR (vinsL 0 (us.map (ev ρ)) ρ) (subE ρ η ts.reverse) u rt ws := by
  rw [show VR ρ η (substTs ts.reverse 0 0 (instT us 0 u)) rt ws ↔ _ from
    VR_substTs ts.reverse η ρ _ [] 0 ρ rt ws (fun k => rfl), VR_instTs]
  rfl


/-! ### Row 18's callee view is coherent -/

theorem Coh_subE {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} (hc : Coh η) : Coh (subE ρ₀ η σs) := by
  have hE : CE (subE ρ₀ η σs) = CE η := rfl
  intro k
  rw [hE]
  cases hk : σs[k]? with
  | some σ =>
      rw [subE_wit_lt hk, subE_rels_lt hk]
      refine ⟨Clo_cl (fun j => (hc j).1) ρ₀ σ, fun ρ' S ws => ?_, fun ρ' S ws => ?_⟩
      · have h := VR_close hc ρ₀ σ [] 0 ρ₀ ρ' S ws (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
        exact h
      · have e : (subE ρ₀ η σs).urels k = fun rt ws => VR ρ₀ η.unsee σ rt ws := by
          simp only [subE, hk]
        have hE' : CE (subE ρ₀ η σs).unsee = CE η.unsee := rfl
        rw [e, hE']
        exact VR_close hc.unsee ρ₀ σ [] 0 ρ₀ ρ' S ws (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
  | none =>
      have hl : σs.length ≤ k := by simpa using hk
      have e : (subE ρ₀ η σs).urels k = η.urels (k - σs.length) := by
        simp only [subE, hk]
      have hE' : CE (subE ρ₀ η σs).unsee = CE η.unsee := rfl
      rw [subE_wit_ge hl, subE_rels_ge hl, e, hE']
      exact hc _


theorem VRR_shiftIN (η : TEnv) (σ : Ty) (rt : Shp) (ws : List Word) (X : Res) :
    ∀ (d : Nat) (ρ : Nat → Nat), VRR ρ η (shiftIN d σ) rt ws X ↔ VRR (fun k => ρ (k + d)) η σ rt ws X
  | 0, ρ => by simp [shiftIN]
  | d + 1, ρ => by
      have h := VRR_shift η (shiftIN d σ) 0 (ρ 0) (fun k => ρ (k + 1)) rt ws X
      rw [vcons_eta] at h
      simp only [shiftIN]
      rw [h, VRR_shiftIN η σ rt ws X d]
      have : (fun k => ρ (k + d + 1)) = (fun k => ρ (k + (d + 1))) := by funext k; rfl
      simp only [Nat.add_assoc] at this ⊢

theorem subE_rrs_lt {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} {σ : Ty} (hk : σs[k]? = some σ) :
    (subE ρ₀ η σs).rrs k = fun S ws X => VRR ρ₀ η σ S ws X := by
  simp only [subE, hk]

theorem subE_rrs_ge {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} {k : Nat} (hl : σs.length ≤ k) :
    (subE ρ₀ η σs).rrs k = η.rrs (k - σs.length) := by
  have : σs[k]? = none := List.getElem?_eq_none hl
  simp only [subE, this]

theorem VRR_substTs (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) :
    ∀ (t : Ty) (P : List Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (X : Res), (∀ k, ρ (k + d) = ρ₀ k) →
      (VRR ρ (TEnv.pre P η) (substTs σs P.length d t) rt ws X ↔ VRR ρ (TEnv.pre P (subE ρ₀ η σs)) t rt ws X)
  | .tvar k, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs]
      by_cases hkc : k < P.length
      · simp only [hkc, if_true, VRR, pre_rrs]
      · simp only [hkc, if_false]
        cases hk : σs[k - P.length]? with
        | some σ =>
            dsimp only
            rw [VRR_shiftIN, VRR_shiftTN]
            simp only [VRR, pre_rrs, hkc, if_false, subE_rrs_lt hk]
            have : (fun k => ρ (k + d)) = ρ₀ := funext hρ
            rw [this]
            exact ⟨fun h => ⟨ws, WLe_refl ws, h⟩, fun ⟨ws', e, h⟩ => VRR_up _ _ _ _ _ e h⟩
        | none =>
            dsimp only
            have hl : σs.length ≤ k - P.length := by simpa using hk
            have h1 : ¬ (k - σs.length < P.length) := by omega
            simp only [VRR, pre_rrs, hkc, h1, if_false, subE_rrs_ge hl]
            rw [show k - σs.length - P.length = k - P.length - σs.length by omega]
  | .refine t ψ, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR, pre_ini, subE_ini]; exact and_congr (VRR_substTs σs η ρ₀ t P d ρ rt ws X hρ) (by rw [TEnv.selIni_substTs σs η ρ₀])
  | .iex b, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      exact VRR_substTs σs η ρ₀ b P (d + 1) (vcons v ρ) rb ws X
        (fun k => by rw [← Nat.add_assoc, vcons_succ]; exact hρ k)
  | .prod a b, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR]
      refine exists_congr fun ra => exists_congr fun rb => and_congr_right fun _ =>
        exists_congr fun Ra => exists_congr fun Rb => and_congr_right fun _ => and_congr_right fun _ =>
        forall_congr' fun n => imp_congr_right fun _ => and_congr_right fun _ => ?_
      rw [VRR_substTs σs η ρ₀ a P d ρ _ _ _ hρ, VRR_substTs σs η ρ₀ b P d ρ _ _ _ hρ]
  | .sum a b, P, d, ρ, rt, ws, X, hρ => by
      have ha := fun rt ws X => VRR_substTs σs η ρ₀ a P d ρ rt ws X hρ
      have hb := fun rt ws X => VRR_substTs σs η ρ₀ b P d ρ rt ws X hρ
      have hau := fun rt ws X => VRR_substTs σs η.unsee ρ₀ a P d ρ rt ws X hρ
      have hbu := fun rt ws X => VRR_substTs σs η.unsee ρ₀ b P d ρ rt ws X hρ
      simp only [substTs, VRR, pre_box, pre_tid, pre_seen, pre_pfr, subE_box, subE_tid, subE_seen, subE_pfr, unsee_pre, subE_unsee, ha, hb, hau, hbu]
  | .code a b, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR, pre_prog, subE_prog, cl_subE σs η ρ₀ P d ρ hρ]
  | .tex κ b, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VRR_substTs σs η ρ₀ b (s :: P) d ρ rb ws X hρ
  | .unit, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .void, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .array _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .ptr _ _, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen,
        cl_subE σs η ρ₀ P d ρ hρ]
  | .ptrOpt _ _, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen,
        cl_subE σs η ρ₀ P d ρ hρ]
  | .loc _ _, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR, pre_sto, pre_tid, pre_pfr, pre_seen, pre_ini, pre_rini, subE_sto, subE_tid, subE_pfr,
        subE_seen, subE_ini, subE_rini, cl_subE σs η ρ₀ P d ρ hρ]
  | .share _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .cap _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .word _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .tok _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .word2 _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .tok2 _ _ _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .epair _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .tokE _ _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .mu b, P, d, ρ, rt, ws, X, hρ => by
      have e := cl_subE σs η ρ₀ P d ρ hρ (.mu b)
      simp only [substTs] at e
      simp only [substTs, VRR, e]
      exact VRR_substTs σs η ρ₀ b (_ :: P) d ρ rt ws X hρ
  | .iall b, P, d, ρ, rt, ws, X, hρ => by
      simp only [substTs, VRR]
      exact forall_congr' fun v =>
        VRR_substTs σs η ρ₀ b P (d + 1) (vcons v ρ) rt ws X (fun k => by rw [← Nat.add_assoc, vcons_succ]; exact hρ k)
  | .intS _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .int, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .tid, _, _, _, _, _, _, _ => by simp only [substTs, VRR, VR, pre_sto, pre_tid, pre_pfr, pre_seen, subE_sto, subE_tid, subE_pfr, subE_seen]
  | .fix _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]
  | .lanes _ _, _, _, _, _, _, _, _ => by simp [substTs, VRR]

/-! ### (P3 c) Pure `let`s in the resourceful frame -/

/-- Types whose values are plain numbers. -/
def FlatT : Ty → Prop
  | .intS _ => True
  | .int => True
  | .fix _ _ => True
  | .lanes _ _ => True
  | _ => False

theorem VRR_flat {ρ : Nat → Nat} {η : TEnv} {t : Ty} {S : Shp} {ws : List Word} (hf : FlatT t)
    (hv : VR ρ η t S ws) : VRR ρ η t S ws .zero := by
  cases t <;> simp_all [FlatT, VR, VRR]

theorem RetOKR_push {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty}
    {K : TEnv → Nat → List Word → Res → Prop} (w : Nat)
    (h : RetOKR ρ η σs ret K) : RetOKR (vcons w ρ) η σs (ret.shiftI 0) K := by
  intro η' he ws R hv hl
  have e := skel_close_shiftI σs ret 0
  rw [shp_of_skel e] at hv
  refine h η' he ws R ((VRR_shift η' ret 0 w ρ _ ws R).1 hv) ⟨ShapeC_wc (wc_of_skel e) hl.1, rfl, ?_, Valid_of_skel e hl.2.2.2.1, rfl⟩
  rw [← wc_of_skel e]; exact hl.2.2.1

theorem pushR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {Rf : Res} (n : String) (w : Nat) (hi : FInvR ρ η σs K cx env Rf) :
    FInvR (vcons w ρ) η σs K (cx.push n) env Rf :=
  ⟨push_FInv n w hi.1, RetOKR_push w hi.2.1, push_HeldOK n w hi.2.2⟩

/-- **Using an atom** in a resourceful frame. -/
theorem useR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx c₁ : Cx} {env : Env} {a : At} {t : Ty} {Rf : Res}
    (h : cx.use a = .ok (t, c₁)) (hi : FInvR ρ η σs K cx env Rf) (hcr : CohR η) :
    ∃ rt ws R Rr, evalAt env a = some (rt, ws) ∧ VR ρ η t (shp rt) ws ∧ Lay σs t rt ws ∧
      VRR ρ η t (shp rt) ws R ∧ FInvR ρ η σs K c₁ env Rr ∧ R + Rr ≤ Rf := by
  obtain ⟨hi1, rt, ws, he, hv, hl⟩ := use_FInv h hi.1
  obtain ⟨rt', ws', R, Rr, he', hvr, hH, hle⟩ := use_HeldOK h hi.2.2 hi.1.2.2.2.2.2.2.2.2.1 hcr
  rw [he] at he'
  simp only [Option.some.injEq, Prod.mk.injEq] at he'
  obtain ⟨rfl, rfl⟩ := he'
  have hret : c₁.ret = cx.ret := (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) h).2.2.1
  refine ⟨rt, ws, R, Rr, he, hv, hl, hvr, ⟨hi1, ?_, hH⟩, hle⟩
  rw [hret]; exact hi.2.1

/-- **Binding** a value carrying `R` in a resourceful frame. -/
theorem bindR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx c' : Cx} {env : Env} {x : String} {t rt : Ty} {ws : List Word} {R Rf : Res}
    (h : cx.bind x t = .ok c') (hi : FInvR ρ η σs K cx env Rf) (hL : RLink η)
    (hvr : VRR ρ η t (shp rt) ws R) (hl : Lay σs t rt ws) :
    FInvR ρ η σs K c' ((x, rt, ws) :: env) (Rf + R) := by
  refine ⟨bind_FInv h hi.1 (VRR_VR t hL hvr) hl, ?_, bind_HeldOK h hi.2.2 hvr⟩
  have := bind_eq h; subst this; exact hi.2.1

/-- **Binding** a plain number: nothing is added. -/
theorem bindR0 {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx c' : Cx} {env : Env} {x : String} {t rt : Ty} {ws : List Word} {Rf : Res}
    (h : cx.bind x t = .ok c') (hi : FInvR ρ η σs K cx env Rf)
    (hv : VR ρ η t (shp rt) ws) (hl : Lay σs t rt ws) (hf : FlatT t) :
    FInvR ρ η σs K c' ((x, rt, ws) :: env) Rf := by
  have := bind_HeldOK h hi.2.2 (VRR_flat hf hv)
  rw [Res.add_zero] at this
  refine ⟨bind_FInv h hi.1 hv hl, ?_, this⟩
  have := bind_eq h; subst this; exact hi.2.1

/-- **P3, pure operations.**  A pure `let` keeps the frame's holdings: a value
moved or paired takes its parts' resources, a number carries none. -/
theorem pure_presR {p : Prog} {cx c' : Cx} {x : String} {op : Op} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {env : Env} {g : G} {s s' : St} {rt : Ty} {ws : List Word}
    {Rf : Res} (hT : OpT p cx x op c') (hA : PureOp op) (hi : FInvR ρ η σs K cx env Rf)
    (hr : (s', rt, ws) ∈ evalOp g env σs s op) (hw : ∀ k, Clo (η.wit k)) (hL : RLink η) (hcr : CohR η) :
    ∃ ρ', FInvR ρ' η σs K c' ((x, rt, ws) :: env) Rf := by
  cases hT <;> simp only [PureOp, PackOK] at hA
  case atom a t c₁ hu hb =>
    obtain ⟨rt0, ws0, R0, Rr, he, hiv, hs, hvr, hi1, hle⟩ := useR hu hi hcr
    simp only [evalOp, he, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, FInvR_mono (bindR hb hi1 hL hvr hs) (by rw [Res.add_comm]; exact hle)⟩
  case pair =>
    rename_i hua hub hbd
    obtain ⟨rta, wa, Ra, Rr1, hea, hva, hsa, hra, hi1, hle1⟩ := useR hua hi hcr
    obtain ⟨rtb, wb, Rb, Rr2, heb, hvb, hsb, hrb, hi2, hle2⟩ := useR hub hi1 hcr
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    refine ⟨ρ, FInvR_mono (bindR (R := Ra + Rb) hbd hi2 hL ?_ (Lay_pair hsa hsb)) ?_⟩
    · show VRR ρ η (.prod _ _) (shp (.prod rta rtb)) (wa ++ wb) (Ra + Rb)
      simp only [VRR]
      refine ⟨shp rta, shp rtb, rfl, Ra, Rb, rfl, fun hn => ?_, fun n hn => ?_⟩
      · rw [shp_wc] at hn; exact absurd hn hsa.2.2.1
      · rw [shp_wc] at hn
        obtain ⟨us, hu, rfl⟩ := wc_some hn
        have hl := hsa.1 us hu
        rw [← hl]
        exact ⟨by simp, by simpa using hra, by simpa using hrb⟩
    · intro k
      have h1 := hle1 k
      have h2 := hle2 k
      simp only [Res.add_apply] at h1 h2 ⊢
      omega
  case addS a b t u i j ha hb hti htj hbd =>
    obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.1.2.1 ha hti
    obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.1.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp [VR, addW, hwa, hwb, ev]) (Lay_int _ rfl) trivial⟩
  case addI a b t u o o' ha hb hti htj hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 ha hti
    obtain ⟨rb, wb, nb, heb, hwb⟩ := atom_int hi.1.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨na + nb, by simp [addW, hwa, hwb]⟩)
      (Lay_int _ rfl) trivial⟩
  case subS a b t u i j d ha hb hti htj hent hbd =>
    obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.1.2.1 ha hti
    obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.1.2.1 hb htj
    simp only [evalOp, hea, heb, ol, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have e := hent ρ hi.1.1
    refine ⟨ρ, bindR0 hbd hi ?_ (Lay_int _ rfl) trivial⟩
    simp [VR, subW, hwa, hwb]; omega
  case nameI a j hj hbd =>
    obtain ⟨t, hpt, hti⟩ := hj
    obtain ⟨ra, wa, hea, hwa, hsa⟩ := atom_num hi.1.2.1 hpt hti
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hp := pushR x (ev ρ j) hi
    refine ⟨vcons (ev ρ j) ρ, bindR0 hbd ⟨⟨Sat_cons hp.1.1 ?_, hp.1.2⟩, hp.2.1, hp.2.2⟩ ?_ (Lay_retype hti rfl hsa) trivial⟩
    · rw [vcons_zero, ev_shift]
    · simp [VR, ev, vcons_zero, hwa]
  case rem a n ta o j v hta hio hj hjv hbd =>
    obtain ⟨tn, hpn, htn⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 hta hio
    obtain ⟨rn, wn, hen, hwn, -⟩ := atom_num hi.1.2.1 hpn htn
    have em : ev ρ j = ρ v + 1 := by simpa [ev] using hjv ρ hi.1.1
    simp only [evalOp, hea, hen, ol, numOf, hwa, hwn, em, Option.bind_eq_bind, Option.bind_some,
      pure, Nat.add_one_ne_zero, beq_iff_eq, ite_false, Option.toList_some,
      List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hk : na % (ρ v + 1) < ρ v + 1 := Nat.mod_lt _ (Nat.succ_pos _)
    let k := na % (ρ v + 1)
    have h1 := pushR (x ++ "_d") (ρ v - k) hi
    have h2 := pushR x k h1
    refine ⟨vcons k (vcons (ρ v - k) ρ), bindR0 hbd ⟨⟨Sat_cons h2.1.1 ?_, h2.1.2⟩, h2.2.1, h2.2.2⟩ ?_ (Lay_int _ rfl) trivial⟩
    · simp only [ev, vcons_zero]
      rw [show v + 2 = (v + 1) + 1 from rfl, vcons_succ, vcons_succ,
        show (1 : Nat) = 0 + 1 from rfl, vcons_succ, vcons_zero]
      omega
    · simp [VR, ev, vcons_zero, k]
  case bits o a b ta tb oa ob ha hb hoa hob hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 ha hoa
    obtain ⟨rb, wb, nb, heb, hwb⟩ := atom_int hi.1.2.1 hb hob
    simp only [evalOp, hea, heb, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl) trivial⟩
  case bit1 o a ta oa ha hoa hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 ha hoa
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl) trivial⟩
  case vmatch lo hi' b t1 t2 t3 o1 o2 o3 h1 h2 h3 e1 e2 e3 hbd =>
    obtain ⟨r1, w1, n1, he1, hw1⟩ := atom_int hi.1.2.1 h1 e1
    obtain ⟨r2, w2, n2, he2, hw2⟩ := atom_int hi.1.2.1 h2 e2
    obtain ⟨r3, w3, n3, he3, hw3⟩ := atom_int hi.1.2.1 h3 e3
    simp only [evalOp, he1, he2, he3, ol, numOf, hw1, hw2, hw3, Option.bind_eq_bind, Option.bind_some,
      pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl) trivial⟩
  case cvt sg w a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.1.2.1 ha hc
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _) trivial⟩
  case toInt a ta ha hc hbd =>
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_cvt hi.1.2.1 ha (toIntSrc_cvt hc)
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl) trivial⟩
  case asLanes sg w a ta ha hc hbd =>
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hc
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 ha ho
    simp only [evalOp, hea, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl⟩ (Lay_lanes _ _ _ _) trivial⟩
  case fop o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.1.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.1.2.1 hb hqb
    simp only [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _) trivial⟩
  case fcmp o a b ta tb q ha hb hqa hqb hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.1.2.1 ha hqa
    obtain ⟨wb, nb, heb, hwb, -⟩ := atom_fix hi.1.2.1 hb hqb
    simp only [evalOp, hea, heb, fixOf, ol, numOf, hwa, hwb, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi (by simp only [VR]; exact ⟨_, rfl⟩) (Lay_int _ rfl) trivial⟩
  case fop1 o a ta q ha hqa hbd =>
    obtain ⟨wa, na, hea, hwa, -⟩ := atom_fix hi.1.2.1 ha hqa
    simp only [evalOp, hea, fixOf, ol, numOf, hwa, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    refine ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl, ?_⟩ (Lay_fix _ _ _ _) trivial⟩
    cases o <;> exact fmask_lt _ _
  case lane a j ta tj q ha hqa hpj hl hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.1.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.1.2.1 hpj htj
    simp only [evalOp, hea, hej, lanesOf, ol, numOf, hwa, hwj, Option.bind_eq_bind, Option.bind_some, pure,
      Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl, fmask_lt _ _⟩ (Lay_fix _ _ _ _) trivial⟩
  case setLane a j v ta tj tv q ha hqa hpj hl hv hqv hbd =>
    obtain ⟨o, htj⟩ := Option.isSome_iff_exists.mp hl
    obtain ⟨wa, na, hea, hwa⟩ := atom_lanes hi.1.2.1 ha hqa
    obtain ⟨rj, wj, nj, hej, hwj⟩ := atom_int hi.1.2.1 hpj htj
    obtain ⟨wv, nv, hev, hwv, -⟩ := atom_fix hi.1.2.1 hv hqv
    simp only [evalOp, hea, hej, hev, lanesOf, ol, numOf, hwa, hwj, hwv, Option.bind_eq_bind,
      Option.bind_some, pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact ⟨ρ, bindR0 hbd hi ⟨rfl, _, rfl⟩ (Lay_lanes _ _ _ _) trivial⟩
  case band a m ta o j v hta hio hj hjv hbd =>
    obtain ⟨tm, hpm, htm⟩ := hj
    obtain ⟨ra, wa, na, hea, hwa⟩ := atom_int hi.1.2.1 hta hio
    obtain ⟨rm, wm, hem, hwm, -⟩ := atom_num hi.1.2.1 hpm htm
    have em : ev ρ j = ρ v := by simpa [ev] using hjv ρ hi.1.1
    simp only [evalOp, hea, hem, ol, numOf, hwa, hwm, em, Option.bind_eq_bind, Option.bind_some,
      pure, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    let k := (na % W64) &&& ρ v
    have hk : k ≤ ρ v := Nat.and_le_right
    have h1 := pushR (x ++ "_d") (ρ v - k) hi
    have h2 := pushR x k h1
    refine ⟨vcons k (vcons (ρ v - k) ρ), bindR0 hbd ⟨⟨Sat_cons h2.1.1 ?_, h2.1.2⟩, h2.2.1, h2.2.2⟩ ?_ (Lay_int _ rfl) trivial⟩
    · simp only [ev, vcons_zero]
      rw [show v + 2 = (v + 1) + 1 from rfl, vcons_succ, vcons_succ,
        show (1 : Nat) = 0 + 1 from rfl, vcons_succ, vcons_zero]
      omega
    · simp [VR, ev, vcons_zero, k]
  case pack =>
    rename_i w body t hidx hwf hua hnl hsub hbd
    obtain ⟨rta, wa, R0, Rr, hea, hva, hla, hvr, hi1, hle⟩ := useR hua hi hcr
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have h1 := VRR_sub hi1.1.1 hsub _ _ _ hvr
    have h2 := (VRR_instT _ η _ 0 ρ _ _ _).1 h1
    -- The source's shape is the package body's: skeletons absorb the witness.
    have es : shp rta = shp (substTs σs 0 1 body) := by
      rw [shp_of_eskel hla.2.1]
      unfold close
      rw [shp_sub hsub σs 0 0]
      exact shp_of_skel (skel_subst_instT σs [w] body 0 0 1 0)
    have ew : wc rta = wc (close σs (.iex body)) := by
      rw [← shp_wc, es, shp_wc]
      exact (wc_iex _).symm
    have v1 := Valid_of_eskel hla.2.1 hla.2.2.2.1
    unfold close at v1
    have v2 := Valid_sub hsub σs 0 0 _ v1
    have v3 := Valid_of_skel (skel_subst_instT σs [w] body 0 0 1 0) v2
    refine ⟨ρ, FInvR_mono (bindR hbd hi1 hL ?_ ⟨ShapeC_wc ew hla.1, rfl, ew ▸ hla.2.2.1,
      by simpa only [close, substTs, Valid] using v3, rfl⟩) (by rw [Res.add_comm]; exact hle)⟩
    simp only [close, substTs, shp, VRR]
    refine ⟨_, _, ev ρ w, rfl, ?_⟩
    rw [← es]
    simpa using h2
  case packT =>
    rename_i σ body t κ hg hwf had hua hnl hsub hbd
    obtain ⟨rta, wa, R0, Rr, hea, hva, hla, hvr, hi1, hle⟩ := useR hua hi hcr
    simp only [evalOp, hea, ol, Option.map_some, Option.toList_some, List.mem_singleton,
      Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have h1 := VRR_sub hi1.1.1 hsub _ _ _ hvr
    -- T3c: the witness is `σ`'s closure; `σ`'s relation is not read (guarded)
    have e1 : Ty.substT 0 σ body = substTs [σ] 0 0 body := substT_eq σ body 0 0
    rw [e1] at h1
    have h3 := (VRR_substTs [σ] η ρ body [] 0 ρ _ _ _ (fun _ => rfl)).1 h1
    have hr1 : ∀ k, k ≠ 0 → (TEnv.pre [] (subE ρ η [σ])).rrs k = (η.push0 (cl ρ η.wit 0 0 σ)).rrs k := by
      intro k hk
      cases k with
      | zero => exact absurd rfl hk
      | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
    have hw1 : (TEnv.pre [] (subE ρ η [σ])).wit = (η.push0 (cl ρ η.wit 0 0 σ)).wit := by
      funext k; cases k <;> simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]
    have h2 := (VRR_relsG body 0 _ (η.push0 (cl ρ η.wit 0 0 σ)) ρ _ _ _ (unguarded_of_guardT hg) hr1
      (fun k hk => by cases k with | zero => exact absurd rfl hk | succ k => simp [TEnv.pre, subE, TEnv.push0, TEnv.ins, TEnv.insR]) hw1 rfl).1 h3
    -- The witness sits under references only: signatures do not see it.
    have eσ := sig_pack σs body 0 0 σ hg
    have es : shp rta = shp (substTs σs 1 0 body) := by
      rw [shp_of_eskel hla.2.1]
      unfold close
      rw [shp_sub hsub σs 0 0]
      exact shp_of_sig eσ
    have ew : wc rta = wc (close σs (.tex κ body)) := by
      rw [← shp_wc, es, shp_wc]
      exact (wc_tex _ _).symm
    have v1 := Valid_of_eskel hla.2.1 hla.2.2.2.1
    unfold close at v1
    have v2 := Valid_sub hsub σs 0 0 _ v1
    have v3 := Valid_of_sig eσ v2
    refine ⟨ρ, FInvR_mono (bindR hbd hi1 hL ?_ ⟨ShapeC_wc ew hla.1, rfl, ew ▸ hla.2.2.1,
      by simpa only [close, substTs, Valid] using v3, rfl⟩) (by rw [Res.add_comm]; exact hle)⟩
    simp only [close, substTs, shp, VRR]
    refine ⟨_, _, cl ρ η.wit 0 0 σ, rfl, Clo_cl hw ρ σ,
      ⟨arrFree_cl hi.1.2.2.2.2.2.2.1.af σ 0 0 (admitsIn_arrFree had), fun hsh =>
        coupledOK_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.1.2.2.2.2.2.2.2.1 k hk) (admitsIn_share had hsh)
          (tb_of_wf σ (admitsIn_wf had)), fun hcp =>
        AffineCl.affine_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.1.2.2.2.2.2.2.2.2.1 k hk) σ
          ((admitsIn_word had).2 hcp) (tb_of_wf σ (admitsIn_wf had)), fun hno =>
        NoOwnCl.noOwn_cl0 ρ η.wit cx.ke hw (fun k _ hk => hi.1.2.2.2.2.2.2.2.2.2.1 k hk) σ
          (admitsIn_noOwn had hno) (tb_of_wf σ (admitsIn_wf had)), fun hsh =>
        rgnFree_cl0 ρ η.wit cx.ke (fun k hk => hi.1.2.2.2.2.2.2.2.2.2.2 k hk) (admitsIn_share had hsh)
          (hA.1 hsh), noIallV_cl hi.1.2.2.2.2.2.2.1.ni σ 0 0 hA.2,
        TermTv.mg_cl (fun k => (hw k).1) hi.1.2.2.2.2.2.2.1.mg σ 0 0 (mg_of_wf σ (admitsIn_wf had))⟩, ?_⟩
    rw [← es]
    exact h2

/-- **P3 at the thread, pure `let`.**  The thread's bound is unchanged. -/
theorem tstep_pureR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {op : Op} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x op e) (hA : PureOp op) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  have _ := hT
  rw [hterm] at hCk
  obtain ⟨c₁, -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hne := pure_progress g (stOf mem pairs th) hop hA hi.1
  have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map
      fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    cases op <;> simp only [PureOp] at hA <;> simp [tstep, hterm]
  rw [key]
  refine ⟨by simpa using hne, ?_⟩
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
  obtain ⟨ρ', h'⟩ := pure_presR hop hA hi hm (fun k => (hE.2.1 k).1) (RLink_of hE.2.1 hE.2.2) hE.2.2
  exact ⟨ρ', η, c₁, Rf, Rs, rfl, hE, ⟨he, hck⟩, OpT_TvOK hP hop htv, h', rfl,
    retPw_skel hPS hpw (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0)⟩


/-! ### (P3 c2) Frame-only control steps, resourceful -/

/-- `ifeq`'s false branch: the context `NoCx` builds is witnessed. -/
theorem noCx_presR {cx c' : Cx} {i j : Idx} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {env : Env}
    (hn : NoCx cx i j c') {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res} (hi : FInvR ρ η σs K cx env Rf) (hne : ev ρ i ≠ ev ρ j) :
    ∃ ρ', FInvR ρ' η σs K c' env Rf := by
  cases hn with
  | same => exact ⟨ρ, hi⟩
  | nzL h1 h2 =>
      rename_i u s
      have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1
      simp only [ev] at e1 e2
      have hu : 1 ≤ ρ u := by
        rcases Nat.eq_zero_or_pos (ρ u) with h | h
        · rw [h] at e1; simp at e1; omega
        · exact h
      have hp := pushR "_nz" (ρ u - 1) hi
      refine ⟨vcons (ρ u - 1) ρ, ⟨Sat_cons hp.1.1 ?_, hp.1.2⟩, hp.2.1, hp.2.2⟩
      simp only [ev, vcons_succ, vcons_zero]; omega
  | nzR h1 h2 =>
      rename_i u s
      have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1
      simp only [ev] at e1 e2
      have hu : 1 ≤ ρ u := by
        rcases Nat.eq_zero_or_pos (ρ u) with h | h
        · rw [h] at e1; simp at e1; omega
        · exact h
      have hp := pushR "_nz" (ρ u - 1) hi
      refine ⟨vcons (ρ u - 1) ρ, ⟨Sat_cons hp.1.1 ?_, hp.1.2⟩, hp.2.1, hp.2.2⟩
      simp only [ev, vcons_succ, vcons_zero]; omega

/-- **P1 + P4, `ifeq`.**  Both operands are one `num` word (so the machine steps),
and whichever branch it takes is well typed in a context the run witnesses. -/
theorem ifeq_stepR {p : Prog} {cx : Cx} {a b : At} {yes no : Expr} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {env : Env} (hT : TermA4.CkW p η.wit cx (.ifeq a b yes no)) {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res} (hi : FInvR ρ η σs K cx env Rf) (htv : TvOK cx) :
    (∃ ra wa rb wb n m, evalAt env a = some (ra, [wa]) ∧ evalAt env b = some (rb, [wb]) ∧
      wa.val = .num n ∧ wb.val = .num m ∧
      (n = m → ∃ ρ' cy, TypedK p η cy yes ∧ TvOK cy ∧ skel cy.ret = skel cx.ret ∧ FInvR ρ' η σs K cy env Rf) ∧
      (n ≠ m → ∃ ρ' cn, TypedK p η cn no ∧ TvOK cn ∧ skel cn.ret = skel cx.ret ∧ FInvR ρ' η σs K cn env Rf)) ∨
    (∃ ra wa rb wb la lb, evalAt env a = some (ra, [wa]) ∧ evalAt env b = some (rb, [wb]) ∧
      wa.val = .loc ⟨la, 0⟩ 0 ∧ wb.val = .loc ⟨lb, 0⟩ 0 ∧ TypedK p η cx yes ∧ TypedK p η cx no) := by
  cases TermA4.CkW_inv_ifeq hT with
  | ifeqPlain hpe hy hn =>
      rcases atom_plainEq hi.1.2.1 hpe with ⟨⟨ra, wa, n, hea, hwa⟩, ⟨rb, wb, m, heb, hwb⟩⟩ |
          ⟨⟨ra, wa, la, hea, hwa⟩, ⟨rb, wb, lb, heb, hwb⟩⟩
      · exact Or.inl ⟨ra, wa, rb, wb, n, m, hea, heb, hwa, hwb, fun _ => ⟨ρ, cx, hy.tk, htv, rfl, hi⟩,
          fun _ => ⟨ρ, cx, hn.tk, htv, rfl, hi⟩⟩
      · exact Or.inr ⟨ra, wa, rb, wb, la, lb, hea, heb, hwa, hwb, hy.tk, hn.tk⟩
  | ifeq hia hib hy hnc hn =>
      rename_i c' i j
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.1.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.1.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun _ => ⟨ρ, cx, hy.tk, htv, rfl, hi⟩, fun hne => ?_⟩
      obtain ⟨ρ', h'⟩ := noCx_presR hnc hi hne
      exact ⟨ρ', c', hn.tk, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩
  | ifeqRec hia hib hrec hy hnc hn =>
      rename_i c' i j t v
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.1.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.1.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun heq => ?_, fun hne => ?_⟩
      · refine ⟨ρ, _, hy.tk, htv, rfl, ⟨Sat_cons hi.1.1 ?_, hi.1.2⟩, hi.2.1, hi.2.2⟩
        rcases hrec with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1; simp only [ev] at e1; omega
        · have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1; simp only [ev] at e1; omega
      · obtain ⟨ρ', h'⟩ := noCx_presR hnc hi hne
        exact ⟨ρ', c', hn.tk, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩
  | ifeqZero hia hib hz hy hnc hn =>
      rename_i c' i j u s
      obtain ⟨ta, hpa, hta⟩ := hia; obtain ⟨tb, hpb, htb⟩ := hib
      obtain ⟨ra, wa, hea, hwa, -⟩ := atom_num hi.1.2.1 hpa hta
      obtain ⟨rb, wb, heb, hwb, -⟩ := atom_num hi.1.2.1 hpb htb
      refine Or.inl ⟨ra, wa, rb, wb, _, _, hea, heb, hwa, hwb, fun heq => ?_, fun hne => ?_⟩
      · refine ⟨ρ, _, hy.tk, htv, rfl, ⟨Sat_cons hi.1.1 ?_, hi.1.2⟩, hi.2.1, hi.2.2⟩
        obtain ⟨hs, hz⟩ := hz
        simp only [ev]
        rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1; simp only [ev] at e1 e2
          rw [heq, e2] at e1
          exact (Nat.mul_eq_zero.1 e1.symm).resolve_left (by omega)
        · have e1 := h1 ρ hi.1.1; have e2 := h2 ρ hi.1.1; simp only [ev] at e1 e2
          rw [← heq, e2] at e1
          exact (Nat.mul_eq_zero.1 e1.symm).resolve_left (by omega)
      · obtain ⟨ρ', h'⟩ := noCx_presR hnc hi hne
        exact ⟨ρ', c', hn.tk, NoCx_TvOK hnc htv, NoCx_retSk hnc, h'⟩

/-- **P1 + P4, `parity`.**  The operand is one `num` word, and the halving
facts of either branch are witnessed. -/
theorem parity_stepR {p : Prog} {cx : Cx} {a : At} {k : String} {ev₀ od : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} (hT : TermA4.CkW p η.wit cx (.parity a k ev₀ od)) {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res} (hi : FInvR ρ η σs K cx env Rf)
    (htv : TvOK cx) :
    ∃ r w n, evalAt env a = some (r, [w]) ∧ w.val = .num n ∧
      (n % 2 = 0 → ∃ ρ' c, TypedK p η c ev₀ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ' η σs K c env Rf) ∧
      (n % 2 ≠ 0 → ∃ ρ' c, TypedK p η c od ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ' η σs K c env Rf) := by
  cases TermA4.CkW_inv_parity hT with
  | parity hia hv he ho =>
      rename_i i v
      obtain ⟨ta, hpa, hta⟩ := hia
      obtain ⟨r, w, hea, hw, -⟩ := atom_num hi.1.2.1 hpa hta
      have e := hv ρ hi.1.1; simp only [ev] at e
      have hp := pushR k (ev ρ i / 2) hi
      refine ⟨r, w, _, hea, hw, fun h0 => ⟨_, _, he.tk, push_TvOK k htv, skel_shiftI cx.ret 0, ⟨Sat_cons hp.1.1 ?_, hp.1.2⟩, hp.2.1, hp.2.2⟩,
        fun h1 => ⟨_, _, ho.tk, push_TvOK k htv, skel_shiftI cx.ret 0, ⟨Sat_cons hp.1.1 ?_, hp.1.2⟩, hp.2.1, hp.2.2⟩⟩
      · simp only [ev, vcons_succ, vcons_zero]; omega
      · simp only [ev, vcons_succ, vcons_zero]; omega


theorem split_stepR {p : Prog} {cx : Cx} {a : At} {x y : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx (.split a x y e)) (hCk : TermA4.CkW p η.wit cx (.split a x y e)) (hi : FInvR ρ η σs K cx env Rf)
    (htv : TvOK cx) (hL : RLink η) (hcr : CohR η) :
    ∃ ra rb ws us, evalAt env a = some (.prod ra rb, ws) ∧ accs ra = some us ∧
      ∃ c, TypedK p η c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ 
        FInvR ρ η σs K c ((y, rb, ws.drop (nWords us)) :: (x, ra, ws.take (nWords us)) :: env) Rf := by
  cases hT with
  | split hu hb1 hb2 he =>
      obtain ⟨rt, ws, R, Rr, hea, -, hl, hvr, hi1, hle⟩ := useR hu hi hcr
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨ra, rb, rfl, hsa, hsb⟩ := eskel_eq_prod hs
      have hsh := hl.1
      have hwa : wc ra ≠ none := by
        intro h; apply hl.2.2.1; simp [wc_prod, h]
      have hwb : wc rb ≠ none := by
        intro h; apply hl.2.2.1; rw [wc_prod, h]; cases wc ra <;> rfl
      obtain ⟨us, hus⟩ : ∃ us, accs ra = some us := by
        cases h : accs ra with
        | none => exact absurd (by simp [wc, h]) hwa
        | some us => exact ⟨us, rfl⟩
      simp only [VRR, shp, Shp.prod.injEq] at hvr
      obtain ⟨sa, sb, ⟨rfl, rfl⟩, Ra, Rb, hR, -, hf⟩ := hvr
      refine ⟨ra, rb, ws, us, hea, hus, ?_⟩
      obtain ⟨hlen, hva, hvb⟩ := hf (nWords us) (by rw [shp_wc]; simp [wc, hus])
      have sha : ShapeC ra (ws.take (nWords us)) := by
        intro us' h'; rw [hus] at h'; simp only [Option.some.injEq] at h'; subst h'
        simp; omega
      have shb : ShapeC rb (ws.drop (nWords us)) := by
        intro ub h'
        have := hsh (us ++ ub) (by simp [accs, hus, h'])
        rw [nWords_append] at this
        simp; omega
      have hvp := hl.2.2.2.1 (nWords us) (by simp [wc, hus])
      have hy := hl.2.2.2.2
      simp only [close, substTs, lyt, etok, Ty.prod.injEq] at hy
      refine ⟨_, ⟨he, TermA4.CkW_split hCk hu hb1 hb2⟩, split_TvOK hu hb1 hb2 htv, by rw [bind_ret hb2, bind_ret hb1, use_ret hu], FInvR_mono (bindR hb2 (bindR hb1 hi1 hL hva ⟨sha, hsa, hwa, hvp.1, hy.1⟩) hL hvb
        ⟨shb, hsb, hwb, hvp.2, hy.2⟩) ?_⟩
      subst hR
      intro k
      have h1 := hle k
      simp only [Res.add_apply] at h1 ⊢
      omega

theorem unpack_stepR {p : Prog} {cx : Cx} {a : At} {i x : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx (.unpack a i x e)) (hCk : TermA4.CkW p η.wit cx (.unpack a i x e)) (hi : FInvR ρ η σs K cx env Rf)
    (htv : TvOK cx) (hL : RLink η) (hcr : CohR η) :
    ∃ rb ws, evalAt env a = some (.iex rb, ws) ∧
      ∃ ρ' c, TypedK p η c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ' η σs K c ((x, rb, ws) :: env) Rf := by
  cases hT with
  | unpack hu hb he =>
      obtain ⟨rt, ws, R, Rr, hea, -, hl, hvr, hi1, hle⟩ := useR hu hi hcr
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨rb, rfl, hsb⟩ := eskel_eq_iex hs
      simp only [VRR, shp, Shp.iex.injEq] at hvr
      obtain ⟨n, sb, w, ⟨-, rfl⟩, hvr⟩ := hvr
      refine ⟨rb, ws, hea, vcons w ρ, _, ⟨he, TermA4.CkW_unpack hCk hu hb⟩, unpack_TvOK hu hb htv, by rw [bind_ret hb, push_ret, skel_shiftI, use_ret hu],
        FInvR_mono (bindR hb (pushR i w hi1) hL hvr ⟨ShapeC_iex hl.1, ?_, ?_, ?_, ?_⟩) ?_⟩
      · rw [hsb]; exact congrArg etok (skel_subst_eq rfl σs 0 1 0)
      · rw [← wc_iex]; exact hl.2.2.1
      · exact hl.2.2.2.1
      · have hy := hl.2.2.2.2
        simp only [close, substTs, lyt, etok, Ty.iex.injEq] at hy
        show etok (lyt 0 rb) = etok (lyt 0 (substTs σs 0 0 _))
        congr 1
        rw [← lyt_down rb 1 0 (by omega), hy, lyt_down _ 1 0 (by omega),
          lyt_substTs _ σs 0 0 1 (by omega), lyt_substTs _ σs 0 0 0 (Nat.le_refl 0)]
      · rw [Res.add_comm]; exact hle

theorem le_of_add_le {R Rr Rf : Res} (h : R + Rr ≤ Rf) : Rr ≤ Rf := fun k => by
  have := h k; simp only [Res.add_apply] at this; omega

theorem ifnull_stepR {p : Prog} {cx : Cx} {a : At} {y : String} {e₁ e₂ : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx (.ifnull a e₁ y e₂)) (hCk : TermA4.CkW p η.wit cx (.ifnull a e₁ y e₂)) (hi : FInvR ρ η σs K cx env Rf)
    (htv : TvOK cx) (hL : RLink η) (hcr : CohR η) :
    ∃ μ u w, evalAt env a = some (.ptrOpt μ u, [w]) ∧
      ((w.val = .null ∧ ∃ c, TypedK p η c e₁ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ η σs K c env Rf) ∨
       (∃ ad, w.val = .loc ad 0 ∧ ∃ c, TypedK p η c e₂ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ η σs K c ((y, .ptr μ u, [w]) :: env) Rf)) := by
  cases hT with
  | ifnull hu he1 hb he2 =>
      obtain ⟨rt, ws, R, Rr, hea, -, hl, hvr, hi1, hle⟩ := useR hu hi hcr
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨μ', u', rfl, hμ, hsu⟩ := eskel_eq_ptrOpt hs
      simp only [VRR] at hvr
      obtain ⟨hv, hR⟩ := hvr
      rcases hv with hn | ⟨ad, cc, hp, hrest⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hn
        exact ⟨μ', u', w, hea, Or.inl ⟨hw, _, ⟨he1, (TermA4.CkW_ifnull hCk hu hb).1⟩, (ifnull_TvOK hu hb htv).1, by rw [use_ret hu], FInvR_mono hi1 (le_of_add_le hle)⟩⟩
      · obtain ⟨w, rfl, hw⟩ := map_singleton hp
        refine ⟨μ', u', w, hea, Or.inr ⟨ad, hw, _, ⟨he2, (TermA4.CkW_ifnull hCk hu hb).2⟩, (ifnull_TvOK hu hb htv).2, by rw [bind_ret hb, use_ret hu],
          FInvR_mono (bindR (R := R) hb hi1 hL ⟨⟨ad, cc, by simp [hw], hrest⟩, hR⟩ ?_) (by rw [Res.add_comm]; exact hle)⟩⟩
        refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs], ⟨ad, by simp [hw]⟩, ?_⟩
        · show Ty.ptr (skelM μ') (etok (skel u')) = Ty.ptr _ _
          rw [hμ, hsu]
        · have hy := hl.2.2.2.2
          simp only [close, substTs, lyt, etok, Ty.ptrOpt.injEq] at hy
          simp only [close, substTs, lyt, etok, hy]

theorem RetOKR_pushT {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {s : Ty} (hc : Coh η) (hs : Clo s)
    (h : RetOKR ρ η σs ret K) : RetOKR ρ (η.consC s) (.unit :: σs) (ret.shiftT 0) K := by
  intro η' he ws R hv hl
  have e : close (.unit :: σs) (ret.shiftT 0) = close σs ret := substTs_cons_shiftT _ _ _ 0 0
  rw [e] at hv
  rw [e] at hl
  let η'' := η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box η'.rid η'.fp η'.rini
  have h2 : Ext η η'' := Ext_withSto hc (fun l c h => he.2.2.2.2.1 l c h) he.2.2.2.2.2.1 he.2.2.2.2.2.2.1
    he.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.2.1 η'.fp η'.rini he.rini
  have hC : CE η'' = CE η' := by
    have hp : η'.prog = η.prog := he.2.2.1
    have ht : η'.tid = η.tid := he.2.2.2.1
    simp only [CE, η'', TEnv.withSto, hp, ht]
  have hv' : VRR ρ (η''.consC s) (ret.shiftT 0) (shp (close σs ret)) ws R :=
    (VRR_coh (Coh_consC h2.1 hs) (CohR_consC h2.2.2.2.2.2.2.2.2.2.2.1 hs) he.1 he.2.2.2.2.2.2.2.2.2.2.1
      he.2.1.symm hC ρ _ _ ws R).2 hv
  have h3 := h η'' h2 ws R ((VRR_shiftTU ret 0 η'' (η''.relC s) s (η''.unsee.relC s) (η''.relCR s)
    (η''.unsee.relCR s) ρ _ ws R).1 hv') ⟨hl.1, rfl, hl.2.2.1, hl.2.2.2.1, rfl⟩
  rw [← hC]; exact h3

theorem HeldOK_pushT {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf : Res} (κ : Kind) (s : Ty)
    (hH : HeldOK ρ η cx env Rf) : HeldOK ρ (η.consC s) (cx.pushT κ) env Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hsum⟩ := hH
  let f : String × Ty × Bool → String × Ty × Bool := fun (y, t, b) => (y, t.shiftT 0, b)
  have hf1 : ∀ e, (f e).1 = e.1 := fun _ => rfl
  have hHf : ∀ e, Holds (cx.pushT κ) (f e) = Holds cx e := fun _ => rfl
  refine ⟨?_, hln, ?_, Rx, ?_, ?_⟩
  · show ((cx.vars.map f).map (·.1)).Nodup
    rw [List.map_map]; exact hn
  · intro y hy
    obtain ⟨⟨y', t', b'⟩, he, h1, h2, h3⟩ := hlent y hy
    exact ⟨f (y', t', b'), List.mem_map_of_mem he, h1, h2, by simpa [f, secondClass_shiftT] using h3⟩
  · intro x e hfe hh
    simp only [Cx.pushT] at hfe
    rw [find_map_flags _ f hf1] at hfe
    cases hf0 : cx.vars.find? (·.1 == x) with
    | none => simp [hf0] at hfe
    | some e0 =>
        simp only [hf0, Option.map_some, Option.some.injEq] at hfe
        subst hfe
        obtain ⟨rt, ws, hl, hv⟩ := hx x e0 hf0 (by rw [← hHf e0]; exact hh)
        exact ⟨rt, ws, hl, (VRR_shiftTU e0.2.1 0 η (η.relC s) s (η.unsee.relC s) (η.relCR s)
          (η.unsee.relCR s) ρ (shp rt) ws (Rx x)).2 hv⟩
  · show Res.sum (((cx.vars.map f).filter (Holds (cx.pushT κ))).map (fun e => Rx e.1)) ≤ Rf
    rw [List.filter_map, List.map_map]
    have : (Holds (cx.pushT κ) ∘ f) = Holds cx := funext hHf
    rw [this]
    exact hsum

theorem pushTR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop}
    {cx : Cx} {env : Env} {Rf : Res} (κ : Kind) (s : Ty) (hc : Coh η) (hs : Clo s) (haf : WitOK κ s)
    (hi : FInvR ρ η σs K cx env Rf) : FInvR ρ (η.consC s) (.unit :: σs) K (cx.pushT κ) env Rf :=
  ⟨pushT_FInv κ s hc hs haf hi.1, RetOKR_pushT hc hs hi.2.1, HeldOK_pushT κ s hi.2.2⟩

theorem unpackT_stepR {p : Prog} {cx : Cx} {a : At} {α x : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx (.unpackT a α x e)) (hCk : TermA4.CkW p η.wit cx (.unpackT a α x e)) (hi : FInvR ρ η σs K cx env Rf) (hc : Coh η) (hcr : CohR η)
    (htv : TvOK cx) :
    ∃ κ rb ws, evalAt env a = some (.tex κ rb, ws) ∧ ∃ s, Clo s ∧
      ∃ c, TypedK p (η.consC s) c e ∧ TvOK c ∧ skel (close (.unit :: σs) c.ret) = skel (close σs cx.ret) ∧
        FInvR ρ (η.consC s) (.unit :: σs) K c ((x, Ty.substT 0 .unit rb, ws) :: env) Rf := by
  cases hT with
  | unpackT hu hg hb he =>
      rename_i κ b
      obtain ⟨rt, ws, R, Rr, hea, -, hl, hvr, hi1, hle⟩ := useR hu hi hcr
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨rb, rfl, hsb⟩ := eskel_eq_tex hs
      simp only [VRR, shp, Shp.tex.injEq] at hvr
      obtain ⟨n, sb, s, ⟨-, rfl⟩, hs, haf, hvr⟩ := hvr
      have hk : skel (Ty.substT 0 .unit rb) = skel (close (.unit :: σs) b) := by
        rw [skel_substT_unit, hsb]; unfold close; rw [skel_substTs, skel_substTs]
        exact substT_substS_unit _ _ 0
      have eσ : sig (Ty.substT 0 .unit rb) = sig rb := by
        have h1 : sig (Ty.substT 0 .unit rb) = sig (close (.unit :: σs) b) := by simp only [sig, hk]
        have h2 : sig rb = sig (substTs σs (0 + 1) 0 b) := by simp only [sig, hsb]
        rw [h1, h2]; unfold close; rw [← substTs_substT_unit]
        exact sig_pack σs b 0 0 .unit hg
      have hL : RLink (η.consC s) := RLink_of (Coh_consC hc hs) (CohR_consC hcr hs)
      refine ⟨_, rb, ws, hea, s, hs, _, ⟨he, TermA4.CkW_unpackT hCk hu hb (fun k => by simp [TEnv.consC, TEnv.insR])⟩, unpackT_TvOK hu hb htv,
        by rw [bind_ret hb]; show skel (substTs (.unit :: σs) 0 0 (((_ : Ty)).shiftT 0)) = _
           rw [substTs_cons_shiftT, use_ret hu]; rfl,
        FInvR_mono (bindR hb (pushTR _ s hc hs haf hi1) hL ?_ ⟨?_, eskel_of_skel hk, ?_, ?_, ?_⟩)
          (by rw [Res.add_comm]; exact hle)⟩
      · rw [shp_of_sig eσ]
        refine (VRR_relsG b 0 (η.push0 s) (η.consC s) ρ _ ws R (unguarded_of_guardT hg) (fun k hk => ?_)
          (fun k hk => ?_) rfl rfl).1 hvr
        all_goals (cases k with
          | zero => exact absurd rfl hk
          | succ k => simp [TEnv.push0, TEnv.ins, TEnv.consC, TEnv.insR])
      · exact ShapeC_wc (wc_of_sig eσ.symm) (ShapeC_wc (wc_tex _ rb) hl.1)
      · rw [wc_of_sig eσ, ← wc_tex _ rb]; exact hl.2.2.1
      · exact Valid_of_sig eσ.symm hl.2.2.2.1
      · have hy := hl.2.2.2.2
        simp only [close, substTs, lyt, etok, Ty.tex.injEq] at hy
        show etok (lyt 0 (Ty.substT 0 .unit rb)) = etok (lyt 0 (substTs (.unit :: σs) 0 0 b))
        congr 1
        rw [lyt_substT_unit, hy.2, ← lyt_substT_unit, substT_substTs_unit]

/-- **P3 at the thread, `ifeq`.** -/
theorem tstep_ifeqR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  have _ := hT
  rw [hterm] at hCk
  rcases ifeq_stepR hCk hi htv with ⟨ra, wa, rb, wb, n, m, hea, heb, hwa, hwb, hy, hn⟩ |
      ⟨ra, wa, rb, wb, la, lb, hea, heb, hwa, hwb, hy, hn⟩
  rotate_left
  · simp only [tstep, hterm, hea, heb, hwa, hwb]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    by_cases h : la = lb
    · exact ⟨ρ, η, cx, Rf, Rs, rfl, hE, by simpa [h] using hy, htv, hi, rfl, retPw_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0)⟩
    · exact ⟨ρ, η, cx, Rf, Rs, rfl, hE, by simpa [h] using hn, htv, hi, rfl, retPw_skel hPS hpw (skel_subst_eq rfl th.σs 0 0 0)⟩
  simp only [tstep, hterm, hea, heb, hwa, hwb]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  by_cases h : n = m
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hy h
    exact ⟨ρ', η, c, Rf, Rs, rfl, hE, by simpa [h] using hc, hvc, hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := hn h
    exact ⟨ρ', η, c, Rf, Rs, rfl, hE, by simpa [h] using hc, hvc, hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P3 at the thread, `parity`.** -/
theorem tstep_parityR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {k : String} {ev₀ od : Expr}
    (hterm : th.term = .parity a k ev₀ od) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  have _ := hT
  rw [hterm] at hCk
  obtain ⟨r, w, n, hea, hw, he, ho⟩ := parity_stepR hCk hi htv
  simp only [tstep, hterm, hea, hw]
  refine ⟨by simp, ?_⟩
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  by_cases h : n % 2 = 0
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := he h
    exact ⟨ρ', η, c, Rf, Rs, rfl, hE, by simpa [h] using hc, hvc, hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨ρ', c, hc, hvc, hk, hf⟩ := ho h
    exact ⟨ρ', η, c, Rf, Rs, rfl, hE, by simpa [h] using hc, hvc, hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P3 at the thread, `split`.** -/
theorem tstep_splitR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  obtain ⟨ra, rb, ws, us, hea, hus, c, hc, hvc, hk, hf⟩ := split_stepR hT hCk hi htv (RLink_of hE.2.1 hE.2.2) hE.2.2
  simp only [tstep, hterm, hea, hus]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P3 at the thread, `unpack`.** -/
theorem tstep_unpackR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  obtain ⟨rb, ws, hea, ρ', c, hc, hvc, hk, hf⟩ := unpack_stepR hT hCk hi htv (RLink_of hE.2.1 hE.2.2) hE.2.2
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ', η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P3 at the thread, `unpackT`** (24e). -/
theorem tstep_unpackTR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {α x : String} {e : Expr}
    (hterm : th.term = .unpackT a α x e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  obtain ⟨κ, rb, ws, hea, s, hs, c, hc, hvc, hk, hf⟩ := unpackT_stepR hT hCk hi hE.2.1 hE.2.2 htv
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨ρ, η.consC s, c, Rf, Rs, rfl, ⟨hE.1, Coh_consC hE.2.1 hs, CohR_consC hE.2.2 hs⟩, hc, hvc, by simpa using hf, rfl, retPw_skel hPS hpw hk⟩

/-- **P3 at the thread, `ifnull`.** -/
theorem tstep_ifnullR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) {Rf Rs : Res} (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  obtain ⟨μ, u, w, hea, h⟩ := ifnull_stepR hT hCk hi htv (RLink_of hE.2.1 hE.2.2) hE.2.2
  rcases h with ⟨hw, c, hc, hvc, hk, hf⟩ | ⟨ad, hw, c, hc, hvc, hk, hf⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · simp only [tstep, hterm, hea, hw]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **`inl`, value level, resourceful.** -/
theorem inl_valueR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {t τ rt : Ty} {ws : List Word} {R : Res}
    (hv : VRR ρ η t (shp rt) ws R) (hl : Lay σs t rt ws)
    (hnb : (Ty.sum rt (close σs τ)).tier ≠ .boxed) :
    ∃ j p q, asArm rt ws = some (j, p) ∧ ofArm (.sum rt (close σs τ)) j p = some q ∧
      VRR ρ η (.sum t τ) (shp (.sum rt (close σs τ))) q R ∧
      Lay σs (.sum t τ) (.sum rt (close σs τ)) q := by
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  have hta := (tier_sum hnb).1
  obtain ⟨j, p, arm, has, harm, hp, q1, hq1, eq1⟩ := asArm_valid rt ws hval hshape hta
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  obtain ⟨q, hq⟩ := encode_ok hnb harmS hp
  obtain ⟨p', hd, ep, hp', q', hq', eq'⟩ := enc_canon hnb harmS hp hq
  obtain ⟨q0, hq0, e0⟩ := ofArm_vals ep hq1
  have e0' : WLe ws q0 := by
    obtain ⟨p'', hd'', ep''⟩ := roundtrip_wle hnb harmS hp hq
    rw [hd] at hd''; cases hd''
    obtain ⟨q0', hq0', e0''⟩ := ofArm_wle ep'' hq1
    rw [hq0] at hq0'; cases hq0'
    exact WLe_trans (asArm_ofArm_wle has hq1 eq1) e0''
  have hlen := ArmsLe.length (arms_lnorm rt)
  refine ⟨j, p, q, has, by simp only [ofArm, sumHead, ite_true]; exact hq, ?_, ?_⟩
  · refine ⟨_, _, _, rfl, Or.inr ⟨j, p', ?_, fun _ => ⟨q0, ofArm_lnorm hq0, ?_⟩, fun h => ?_⟩⟩
    · have := decodeArm_mono (arms_lnorm (.sum rt (close σs τ))) hd
      rw [← tier_lnorm (.sum rt (close σs τ))] at this; exact this
    · rw [shp_lnorm]; exact VRR_up _ _ _ _ _ e0' hv
    · omega
  · refine ⟨shape_sum hq, ?_, wc_sum_ne _ _, ?_, by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
    · show Ty.sum (etok (skel rt)) (etok (skel (close σs τ))) = _
      rw [hsk]; rfl
    · exact Or.inr ⟨j, p', arm, hd, harmS, hp', ⟨q', hq', eq'⟩,
        fun _ => ⟨q0, hq0, ShapeC_vals e0'.vals hshape, hwc, Valid_vals _ _ _ e0'.vals hval⟩,
        fun h => absurd h (by omega)⟩

/-- **`inr`, value level, resourceful.** -/
theorem inr_valueR {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {t τ rt : Ty} {ws : List Word} {R : Res}
    (hv : VRR ρ η t (shp rt) ws R) (hl : Lay σs t rt ws)
    (hnb : (Ty.sum (close σs τ) rt).tier ≠ .boxed) :
    ∃ j p q, asArm rt ws = some (j, p) ∧
      ofArm (.sum (close σs τ) rt) ((armsOf (close σs τ)).length + j) p = some q ∧
      VRR ρ η (.sum τ t) (shp (.sum (close σs τ) rt)) q R ∧
      Lay σs (.sum τ t) (.sum (close σs τ) rt) q := by
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  have hta := (tier_sum hnb).2
  obtain ⟨j, p, arm, has, harm, hp, q1, hq1, eq1⟩ := asArm_valid rt ws hval hshape hta
  generalize hm : (armsOf (close σs τ)).length = m
  have harmS : (armsOf (.sum (close σs τ) rt))[m + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (by omega)]
    rw [hm, Nat.add_sub_cancel_left]; exact harm
  obtain ⟨q, hq⟩ := encode_ok hnb harmS hp
  obtain ⟨p', hd, ep, hp', q', hq', eq'⟩ := enc_canon hnb harmS hp hq
  obtain ⟨q0, hq0, e0⟩ := ofArm_vals ep hq1
  have e0' : WLe ws q0 := by
    obtain ⟨p'', hd'', ep''⟩ := roundtrip_wle hnb harmS hp hq
    rw [hd] at hd''; cases hd''
    obtain ⟨q0', hq0', e0''⟩ := ofArm_wle ep'' hq1
    rw [hq0] at hq0'; cases hq0'
    exact WLe_trans (asArm_ofArm_wle has hq1 eq1) e0''
  have hlen : (armsOf (lnorm (close σs τ))).length = m := by
    rw [← ArmsLe.length (arms_lnorm _)]; exact hm
  refine ⟨j, p, q, has, by simp only [ofArm, sumHead, ite_true]; exact hq, ?_, ?_⟩
  · refine ⟨_, _, _, rfl, Or.inr ⟨m + j, p', ?_, fun h => absurd h (by omega), fun _ => ⟨q0, ?_, ?_⟩⟩⟩
    · have := decodeArm_mono (arms_lnorm (.sum (close σs τ) rt)) hd
      rw [← tier_lnorm (.sum (close σs τ) rt)] at this; exact this
    · rw [hlen, Nat.add_sub_cancel_left]; exact ofArm_lnorm hq0
    · rw [shp_lnorm]; exact VRR_up _ _ _ _ _ e0' hv
  · refine ⟨shape_sum hq, ?_, wc_sum_ne _ _, ?_, by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
    · show Ty.sum (etok (skel (close σs τ))) (etok (skel rt)) = _
      rw [hsk]; rfl
    · refine Or.inr ⟨m + j, p', arm, hd, harmS, hp', ⟨q', hq', eq'⟩, fun h => absurd h (by omega),
        fun _ => ⟨q0, ?_, ShapeC_vals e0'.vals hshape, hwc, Valid_vals _ _ _ e0'.vals hval⟩⟩
      rw [hm, Nat.add_sub_cancel_left]; exact hq0

theorem res_swap_le {R Rr Rf : Res} (h : R + Rr ≤ Rf) : Rr + R ≤ Rf := by
  rw [Res.add_comm]; exact h

/-- **`case`, resourceful.** -/
theorem case_stepR {p : Prog} {cx : Cx} {a : At} {x y : String} {e₁ e₂ : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {env : Env} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx (.case a x e₁ y e₂)) (hCk : TermA4.CkW p η.wit cx (.case a x e₁ y e₂)) (hi : FInvR ρ η σs K cx env Rf)
    (hL : RLink η) (hcr : CohR η)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close σs t).tier ≠ .boxed) (htv : TvOK cx) :
    ∃ ra rb ws j p', evalAt env a = some (.sum ra rb, ws) ∧ (Ty.sum ra rb).tier ≠ .boxed ∧
      asArm (.sum ra rb) ws = some (j, p') ∧
      (j < (armsOf ra).length → ∃ q, ofArm ra j p' = some q ∧
        ∃ c, TypedK p η c e₁ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ η σs K c ((x, ra, q) :: env) Rf) ∧
      ((armsOf ra).length ≤ j → ∃ q, ofArm rb (j - (armsOf ra).length) p' = some q ∧
        ∃ c, TypedK p η c e₂ ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ FInvR ρ η σs K c ((y, rb, q) :: env) Rf) := by
  cases hT with
  | case hu hb1 he1 hb2 he2 =>
      obtain ⟨rt, ws, R, Rr, hea, -, hl, hv, hi1, hle⟩ := useR hu hi hcr
      have hs := hl.2.1
      simp only [close, substTs, skel, etok] at hs
      obtain ⟨ra, rb, rfl, hsa, hsb⟩ := eskel_eq_sum hs
      have hS : (Ty.sum ra rb).tier ≠ .boxed := by
        rw [tier_of_eskel hl.2.1]; exact hnb _ _ hu
      obtain ⟨-, -, -, hval, hly⟩ := hl
      simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
      rcases hval with hbx | ⟨j, p', arm, hd, -, -, -, hA, hB⟩
      · exact absurd hbx hS
      simp only [VRR, shp] at hv
      obtain ⟨n, Ra, Rb, hR, hv⟩ := hv
      simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
      obtain ⟨-, rfl, rfl⟩ := hR
      have htl := tier_lnorm (.sum ra rb)
      simp only [lnorm] at htl
      rcases hv with hbx | ⟨j', p'', hd', hl1, hl2⟩
      · rw [htl] at hbx; exact absurd hbx.1 hS
      have hd2 := decodeArm_mono (arms_lnorm (.sum ra rb)) hd
      simp only [lnorm] at hd2
      rw [htl, hd2] at hd'
      simp only [Option.some.injEq, Prod.mk.injEq] at hd'
      obtain ⟨e1, e2⟩ := hd'
      subst e1; subst e2
      have hlen := ArmsLe.length (arms_lnorm ra)
      refine ⟨ra, rb, ws, j, p', hea, hS, by simp only [asArm, sumHead, ite_true]; exact hd, ?_, ?_⟩
      · intro hj
        obtain ⟨q, hq, hsa', hwa, hva⟩ := hA hj
        obtain ⟨q'', hq'', hvq⟩ := hl1 (by omega)
        rw [ofArm_lnorm hq, Option.some.injEq] at hq''
        subst hq''
        rw [shp_lnorm] at hvq
        exact ⟨q, hq, _, ⟨he1, (TermA4.CkW_case hCk hu hb1 hb2).1⟩, (case_TvOK hu hb1 hb2 htv).1, by rw [bind_ret hb1, use_ret hu],
          FInvR_mono (bindR hb1 hi1 hL hvq ⟨hsa', hsa, hwa, hva, hly.1⟩) (res_swap_le hle)⟩
      · intro hj
        obtain ⟨q, hq, hsb', hwb, hvb⟩ := hB hj
        obtain ⟨q'', hq'', hvq⟩ := hl2 (by omega)
        rw [← hlen, ofArm_lnorm hq, Option.some.injEq] at hq''
        subst hq''
        rw [shp_lnorm] at hvq
        exact ⟨q, hq, _, ⟨he2, (TermA4.CkW_case hCk hu hb1 hb2).2⟩, (case_TvOK hu hb1 hb2 htv).2, by rw [bind_ret hb2, use_ret hu],
          FInvR_mono (bindR hb2 hi1 hL hvq ⟨hsb', hsb, hwb, hvb, hly.2⟩) (res_swap_le hle)⟩

/-- **`inl` at the thread, resourceful.** -/
theorem tstep_inlR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c'
      obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inl _ hu hb =>
          obtain ⟨rt, ws, R, Rr, hea, -, hl, hv, hi1, hle⟩ := useR hu hi hE.2.2
          have hS : (Ty.sum rt (close th.σs τ)).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inl_valueR hv hl hS
          have hta := (tier_sum hS).1
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          have hf := FInvR_mono (bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
          exact ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **`inr` at the thread, resourceful.** -/
theorem tstep_inrR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c'
      obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | inr _ hu hb =>
          obtain ⟨rt, ws, R, Rr, hea, -, hl, hv, hi1, hle⟩ := useR hu hi hE.2.2
          have hS : (Ty.sum (close th.σs τ) rt).tier ≠ .boxed := by
            rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)]
            exact hnb _ _ hu
          obtain ⟨j, q0, q, has, hq, hvr, hlay⟩ := inr_valueR hv hl hS
          have hta := (tier_sum hS).2
          simp only [tstep, hterm, evalOp, hea, projM_nb hta, has, injM_nb hS, hq, ol,
            Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.map_cons, List.map_nil, List.append_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          have hf := FInvR_mono (bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
          exact ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **`case` at the thread, resourceful.** -/
theorem tstep_caseR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {Rf Rs : Res}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  obtain ⟨ra, rb, ws, j, p', hea, hS, has, hA, hB⟩ :=
    case_stepR hT hCk hi (RLink_of hE.2.1 hE.2.2) hE.2.2 hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  by_cases hj : j < (armsOf ra).length
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hA hj
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa [withS] using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩
  · obtain ⟨q, hq, c, hc, hvc, hk, hf⟩ := hB (by omega)
    simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, hq, List.map_cons, List.map_nil,
      List.append_nil]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨ρ, η, c, Rf, Rs, rfl, hE, hc, hvc, by simpa [withS] using hf, rfl, retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-! ### (P3 d) Capability and token steps, resourceful -/

/-- A list of resources, mapped by a name-preserving `F` and filtered, sums as
the original filtered by the pulled-back predicate. -/
theorem sum_map_filter (F : String × Ty × Bool → String × Ty × Bool) (H' H : String × Ty × Bool → Bool)
    (Rx : String → Res) (hF : ∀ e, (F e).1 = e.1) :
    ∀ l : List (String × Ty × Bool), (∀ e ∈ l, H' (F e) = H e) →
      Res.sum (((l.map F).filter H').map (fun e => Rx e.1)) = Res.sum ((l.filter H).map (fun e => Rx e.1))
  | [], _ => rfl
  | e :: l, h => by
      have ih := sum_map_filter F H' H Rx hF l (fun e he => h e (List.mem_cons_of_mem _ he))
      have he := h e List.mem_cons_self
      simp only [List.map_cons, List.filter_cons, he]
      split
      · simp only [List.map_cons, Res.sum_cons, ih, hF e]
      · exact ih

/-- Filtering first only drops summands. -/
theorem sum_filter_le (q H : String × Ty × Bool → Bool) (Rx : String → Res) :
    ∀ l : List (String × Ty × Bool),
      Res.sum (((l.filter q).filter H).map (fun e => Rx e.1)) ≤ Res.sum ((l.filter H).map (fun e => Rx e.1))
  | [] => Res.le_refl _
  | e :: l => by
      have ih := sum_filter_le q H Rx l
      cases hq : q e <;> cases hH : H e <;>
        simp only [List.filter_cons, hq, hH, List.map_cons, Res.sum_cons, Bool.false_eq_true, ite_true, ite_false]
      · exact ih
      · exact Res.le_trans ih (by rw [Res.add_comm]; exact Res.le_add_right _ _)
      · exact ih
      · exact Res.add_le_add (Res.le_refl _) ih

/-- With unique names, a lookup in a filtered context finds the same entry. -/
theorem find_filter_nodup (q : String × Ty × Bool → Bool) (x : String) (e : String × Ty × Bool) :
    ∀ l : List (String × Ty × Bool), (l.map (·.1)).Nodup →
      (l.filter q).find? (·.1 == x) = some e → l.find? (·.1 == x) = some e
  | [], _, h => by simp at h
  | a :: l, hn, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      have ih := find_filter_nodup q x e l hn.2
      cases hq : q a
      · simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false] at h
        have hm := List.mem_of_find?_eq_some h
        have hx := List.find?_some h
        simp only [beq_iff_eq] at hx
        have hne : (a.1 == x) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro hax
          exact hn.1 ⟨e, (List.mem_filter.1 hm).1, by rw [hx, hax]⟩
        simp only [List.find?_cons, hne]
        exact ih h
      · simp only [List.filter_cons, hq, ite_true, List.find?_cons] at h ⊢
        split at h
        · exact h
        · exact ih h

theorem VarsOK_filter {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {vars : List (String × Ty × Bool)} {env : Env}
    (q : String × Ty × Bool → Bool) (hn : (vars.map (·.1)).Nodup) (h : VarsOK ρ η σs vars env) :
    VarsOK ρ η σs (vars.filter q) env :=
  fun x e he => h x e (find_filter_nodup q x e vars hn he)

theorem mem_lent_var {cx : Cx} {y : String} {t : Ty} (hn : (cx.vars.map (·.1)).Nodup)
    (hlent : ∀ y ∈ cx.lent, ∃ e ∈ cx.vars, e.1 = y ∧ e.2.2 = false ∧ e.2.1.secondClass = false)
    (hf : cx.vars.find? (·.1 == y) = some (y, t, true)) : y ∉ cx.lent := by
  intro hm
  obtain ⟨e, he1, rfl, hb, -⟩ := hlent _ hm
  have h1 := List.mem_of_find?_eq_some hf
  have : e = (e.1, t, true) := mem_nodup_eq cx.vars hn e he1 _ h1 rfl
  rw [this] at hb; cases hb

theorem markU_fst (y : String) (e : String × Ty × Bool) : (markU y e).1 = e.1 := by
  simp only [markU]; split <;> rfl

theorem markU_snd (y : String) (e : String × Ty × Bool) : (markU y e).2.1 = e.2.1 := by
  simp only [markU]; split <;> rfl

/-- **Lending** `y` (`borrow`): its resources stay counted, now through `lent`. -/
theorem lend_HeldOK {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf : Res} {y : String} {t : Ty}
    (hH : HeldOK ρ η cx env Rf) (hf : cx.vars.find? (·.1 == y) = some (y, t, true))
    (hsc : t.secondClass = false) :
    HeldOK ρ η
      { cx with
        vars := cx.vars.map (markU y)
        lent := y :: cx.lent } env Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := hH
  have hyl := mem_lent_var hn hlent hf
  have hy1 := List.mem_of_find?_eq_some hf
  have hHf : ∀ e ∈ cx.vars, Holds { cx with vars := cx.vars.map (markU y), lent := y :: cx.lent } (markU y e) =
      Holds cx e := by
    intro e he
    obtain ⟨z, u, b⟩ := e
    by_cases hz : z = y
    · subst hz
      have : (z, u, b) = (z, t, true) := mem_nodup_eq cx.vars hn _ he _ hy1 rfl
      simp only [Prod.mk.injEq] at this
      obtain ⟨-, rfl, rfl⟩ := this
      simp [Holds, markU]
    · have hb : (z == y) = false := by simpa using hz
      simp [Holds, markU, hb, hz]
  refine ⟨?_, List.nodup_cons.2 ⟨hyl, hln⟩, ?_, Rx, ?_, ?_⟩
  · show ((cx.vars.map (markU y)).map (·.1)).Nodup
    rw [List.map_map]
    have : ((·.1) ∘ markU y) = (·.1 : String × Ty × Bool → String) := funext (markU_fst y)
    rw [this]; exact hn
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨markU z (z, t, true), List.mem_map_of_mem hy1, by simp [markU], by simp [markU], by simp [markU, hsc]⟩
    · obtain ⟨e, he1, h1, h2, h3⟩ := hlent z hz
      refine ⟨markU y e, List.mem_map_of_mem he1, by rw [markU_fst]; exact h1, ?_, by rw [markU_snd]; exact h3⟩
      simp only [markU]; split <;> simp_all
  · intro z e hfe hh
    show ∃ rt ws, lookupE env z = some (rt, ws) ∧ VRR ρ η e.2.1 (shp rt) ws (Rx z)
    have hfe' := hfe
    simp only at hfe'
    rw [find_map_flags _ (markU y) (markU_fst y)] at hfe'
    cases hf0 : cx.vars.find? (·.1 == z) with
    | none => simp [hf0] at hfe'
    | some e0 =>
        simp only [hf0, Option.map_some, Option.some.injEq] at hfe'
        subst hfe'
        rw [markU_snd]
        rw [hHf e0 (List.mem_of_find?_eq_some hf0)] at hh
        exact hx z e0 hf0 hh
  · show Res.sum (((cx.vars.map (markU y)).filter
      (Holds { cx with vars := cx.vars.map (markU y), lent := y :: cx.lent })).map (fun e => Rx e.1)) ≤ Rf
    rw [sum_map_filter (markU y) _ (Holds cx) Rx (markU_fst y) cx.vars hHf]
    exact hs

/-- With unique names, an entry is the first one under its name. -/
theorem find_self_nodup : ∀ (l : List (String × Ty × Bool)), (l.map (·.1)).Nodup →
    ∀ e ∈ l, l.find? (·.1 == e.1) = some e
  | [], _, e, he => by cases he
  | a :: l, hn, e, he => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      rcases List.mem_cons.1 he with rfl | he'
      · simp
      · have hne : (a.1 == e.1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h; exact hn.1 ⟨e, he', h.symm⟩
        simp only [List.find?, hne]
        exact find_self_nodup l hn.2 e he'

/-- With unique names, `firstOK` is the second-class test. -/
theorem firstOK_nodup {l : List (String × Ty × Bool)} (hn : (l.map (·.1)).Nodup) {e : String × Ty × Bool}
    (he : e ∈ l) : Cx.firstOK l e = !e.2.1.secondClass := by
  unfold Cx.firstOK; rw [find_self_nodup l hn e he]

/-- `endCx`, named: the lent name erased, second-class variables swept, `y`
live again. -/
theorem endCx_eq (cx : Cx) (y : String) : ∃ F : String × Ty × Bool → String × Ty × Bool,
    cx.endCx y =
      { cx with
        lent := cx.lent.erase y
        vars := (cx.vars.filter (Cx.firstOK cx.vars)).map F } ∧
    ∀ e, (F e).1 = e.1 ∧ (F e).2.1 = e.2.1 ∧ (F e).2.2 = (e.2.2 || e.1 == y) := by
  refine ⟨_, rfl, ?_⟩
  intro e
  obtain ⟨z, u, b⟩ := e
  by_cases hz : z = y
  · subst hz; simp
  · have hb : (z == y) = false := by simpa using hz
    simp [hb]

/-- **Taking a loan back** (`endBorrow`): the lent value is live again and
second-class variables go; the holdings do not grow. -/
theorem endB_HeldOK {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf : Res} {y : String}
    (F : String × Ty × Bool → String × Ty × Bool)
    (hF : ∀ e, (F e).1 = e.1 ∧ (F e).2.1 = e.2.1 ∧ (F e).2.2 = (e.2.2 || e.1 == y))
    (hH : HeldOK ρ η cx env Rf) (hy : y ∈ cx.lent) :
    HeldOK ρ η
      { cx with
        lent := cx.lent.erase y
        vars := (cx.vars.filter (Cx.firstOK cx.vars)).map F } env Rf := by
  obtain ⟨hn, hln, hlent, Rx, hx, hs⟩ := hH
  let q : String × Ty × Bool → Bool := Cx.firstOK cx.vars
  let c₀ : Cx :=
    { cx with
      lent := cx.lent.erase y
      vars := (cx.vars.filter q).map F }
  have hHf : ∀ e, Holds c₀ (F e) = Holds cx e := by
    intro e
    simp only [Holds, c₀, (hF e).1, (hF e).2.2]
    by_cases hz : e.1 = y
    · simp [hz, hy]
    · have hb : (e.1 == y) = false := by simpa using hz
      simp [hb, List.mem_erase_of_ne hz]
  refine ⟨?_, hln.erase y, ?_, Rx, ?_, ?_⟩
  · show (((cx.vars.filter q).map F).map (·.1)).Nodup
    rw [List.map_map]
    have : ((·.1) ∘ F) = (·.1 : String × Ty × Bool → String) := funext fun e => (hF e).1
    rw [this]
    exact hn.sublist ((List.filter_sublist).map _)
  · intro z hz
    obtain ⟨hzy, hz⟩ := (hln.mem_erase_iff).1 hz
    obtain ⟨e, he1, h1, h2, h3⟩ := hlent z hz
    refine ⟨F e, List.mem_map_of_mem (List.mem_filter.2 ⟨he1, by simp [q, firstOK_nodup hn he1, h3]⟩), by rw [(hF e).1]; exact h1,
      ?_, by rw [(hF e).2.1]; exact h3⟩
    have hb : (e.1 == y) = false := by simpa [h1] using hzy
    rw [(hF e).2.2, h2, hb]; rfl
  · intro z e hfe hh
    show ∃ rt ws, lookupE env z = some (rt, ws) ∧ VRR ρ η e.2.1 (shp rt) ws (Rx z)
    have hfe' : ((cx.vars.filter q).map F).find? (·.1 == z) = some e := hfe
    rw [find_map_flags _ F (fun e => (hF e).1)] at hfe'
    cases hf0 : (cx.vars.filter q).find? (·.1 == z) with
    | none => simp [hf0] at hfe'
    | some e0 =>
        simp only [hf0, Option.map_some, Option.some.injEq] at hfe'
        subst hfe'
        rw [(hF e0).2.1]
        have hh' : Holds c₀ (F e0) = true := hh
        rw [hHf e0] at hh'
        exact hx z e0 (find_filter_nodup q z e0 cx.vars hn hf0) hh'
  · show Res.sum ((((cx.vars.filter q).map F).filter (Holds c₀)).map (fun e => Rx e.1)) ≤ Rf
    rw [sum_map_filter F (Holds c₀) (Holds cx) Rx (fun e => (hF e).1) _ (fun e _ => hHf e)]
    exact Res.le_trans (sum_filter_le q (Holds cx) Rx cx.vars) hs

theorem VRR_cap {ρ : Nat → Nat} {η : TEnv} {c : Cap} {r : Idx} {S : Shp} {ws : List Word} :
    VRR ρ η (.cap c r) S ws .zero := by simp [VRR]

theorem Lay_cap (σs : List Ty) (c : Cap) (r : Idx) : Lay σs (.cap c r) (.cap c (.lit 0)) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [ShapeC, accs, nWords, close, substTs, skel, etok, wc, Valid, lyt, idxC, ofMs]

theorem Lay_unitT (σs : List Ty) : Lay σs .unit .unit [] := Lay_etok_unit rfl

/-- The ops whose step touches only the frame: capabilities and tokens. -/
def CapOp : Op → Prop
  | .borrow _ _ | .freeze _ | .endBorrow _ | .claim _ _ => True
  | _ => False

theorem tstep_capOp {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh} {x : String} {op : Op}
    {e : Expr} (hterm : th.term = .let_ x op e) (hA : CapOp op) :
    tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map
      fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
  cases op <;> simp only [CapOp] at hA <;> simp [tstep, hterm]

/-- **P3, the capability steps**: `borrow` lends (the token stays counted, via
`lent`), `endBorrow` takes it back, `freeze` spends it.  The bound never grows. -/
theorem cap_presR {p : Prog} {cx c' : Cx} {x : String} {op : Op} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {env : Env} {g : G} {s s' : St} {rt : Ty} {ws : List Word}
    {Rf : Res} (hT : OpT p cx x op c') (hA : CapOp op) (hncl : ∀ a tk, op ≠ .claim a tk)
    (hi : FInvR ρ η σs K cx env Rf)
    (hr : (s', rt, ws) ∈ evalOp g env σs s op) (hL : RLink η) (hcr : CohR η) :
    FInvR ρ η σs K c' ((x, rt, ws) :: env) Rf := by
  cases hT <;> simp only [CapOp] at hA
  case borrow c₁ y c a t t' r hva hpk hlo hu hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hay : a = .var y := by cases a <;> simp [varOf, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hva ⊢ <;> exact hva
    subst hay
    have htk : (∃ q st, t = .tok q st) ∨ (∃ q P i j, t = .tok2 q P i j) ∨ ∃ q, t = .share q := by
      cases t <;> simp [lendOf, throw, throwThe, MonadExceptOf.throw] at hlo <;> simp
    have hsc : t.secondClass = false := by
      rcases htk with ⟨q, st, rfl⟩ | ⟨q, P, i, j, rfl⟩ | ⟨q, rfl⟩ <;> rfl
    have haf : affine cx.ke t = true := by
      rcases htk with ⟨q, st, rfl⟩ | ⟨q, P, i, j, rfl⟩ | ⟨q, rfl⟩ <;> simp [affine, Ty.affineIn]
    obtain ⟨hp, hc⟩ := use_cases hu
    rw [hpk] at hp
    simp only [Except.ok.injEq] at hp
    subst hp
    rcases hc with ⟨hna, -⟩ | ⟨y', hy', rfl⟩
    · rw [haf] at hna; cases hna
    · simp only [At.var.injEq] at hy'
      subst hy'
      have hf := peek_var hpk
      have hi1 := (use_FInv hu hi.1).1
      have hH := lend_HeldOK hi.2.2 hf hsc
      have hfr : FInvR ρ η σs K { cx with vars := cx.vars.map (markU y), lent := y :: cx.lent } env Rf :=
        ⟨hi1, hi.2.1, hH⟩
      have := bindR (R := .zero) hb hfr hL VRR_cap (Lay_cap σs c r)
      rwa [Res.add_zero] at this
  case freeze c₁ a r hu hsr hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hcr
    have := bindR (R := .zero) hb hi1 hL VRR_cap (Lay_cap σs .frz r)
    rw [Res.add_zero] at this
    exact FInvR_mono this (Res.le_trans (by rw [Res.add_comm]; exact Res.le_add_right _ _) hle)
  case endBorrow y a hva hy hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    obtain ⟨F, hceq, hF⟩ := endCx_eq cx y
    rw [hceq] at hb
    have hyl : y ∈ cx.lent := by simpa using hy
    have hH := endB_HeldOK F hF hi.2.2 hyl
    have hv : VarsOK ρ η σs ((cx.vars.filter (Cx.firstOK cx.vars)).map F) env :=
      VarsOK_flags F (fun e => ⟨(hF e).1, (hF e).2.1⟩) (VarsOK_filter _ hi.2.2.1 hi.1.2.1)
    have hfr : FInvR ρ η σs K
        { cx with
          lent := cx.lent.erase y
          vars := (cx.vars.filter (Cx.firstOK cx.vars)).map F } env Rf :=
      ⟨⟨hi.1.1, hv, hi.1.2.2⟩, hi.2.1, hH⟩
    have := bindR (R := .zero) hb hfr hL (by simp [VRR]) (Lay_unitT σs)
    rwa [Res.add_zero] at this
  case claim => exact absurd rfl (hncl _ _)

/-- **P3, `claim`**: the ticket (an epoch key) is exchanged for the owner's
token (the region key).  The bound grows by the region key and shrinks by
the epoch key. -/
theorem claim_presR {p : Prog} {cx c' : Cx} {x : String} {w : At} {tk : At} {ρ : Nat → Nat} {η : TEnv}
    {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop} {env : Env} {g : G} {s s' : St} {rt : Ty}
    {ws : List Word} {Rf : Res} (hT : OpT p cx x (.claim w tk) c')
    (hi : FInvR ρ η σs K cx env Rf)
    (hr : (s', rt, ws) ∈ evalOp g env σs s (.claim w tk)) (hL : RLink η) (hcr : CohR η) :
    ∃ n j Rf', FInvR ρ η σs K c' ((x, rt, ws) :: env) Rf' ∧
      Rf' + Res.one (.ep n j) ≤ Rf + Res.one (.rg n) := by
  cases hT with
  | claim hpk hw ht hu heq hsaw hj hb =>
    rename_i c₁ wn t rP Q r' j m
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, hvr, hi1, hle⟩ := useR hu hi hcr
    simp only [VRR] at hvr
    subst hvr
    have hn : ev ρ rP.1 = ev ρ r' := heq ρ hi1.1.1
    have := bindR (R := Res.one (.rg (ev ρ rP.1))) hb hi1 hL (by simp [VRR]) (Lay_etok_unit rfl)
    refine ⟨ev ρ r', ev ρ j, _, this, ?_⟩
    rw [hn]
    intro k
    have h1 := hle k
    simp only [Res.add_apply] at h1 ⊢
    omega

/-- **P3 at the thread, the capability steps.** -/
theorem tstep_capR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {op : Op} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x op e) (hA : CapOp op) (hncl : ∀ a tk, op ≠ .claim a tk) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨c₁, -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
      rw [tstep_capOp hterm hA]
      refine ⟨?_, ?_⟩
      · cases op <;> simp only [CapOp] at hA <;> simp [evalOp]
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
      have h' := cap_presR hop hA hncl hi hm (RLink_of hE.2.1 hE.2.2) hE.2.2
      exact ⟨ρ, η, c₁, Rf, Rs, rfl, hE, ⟨he, hck⟩, OpT_TvOK hP hop htv, h', rfl,
        retPw_skel hPS hpw (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0)⟩

/-- **P3 at the thread, `claim`**: the thread's bound trades the epoch key
for the region key. -/
theorem tstep_claimR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {w tk : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.claim w tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ n j Tot',
      ThInvRE p (CE η) r.2.2 Tot' ∧ Tot' + Res.one (.ep n j) ≤ Rf + Rs + Res.one (.rg n) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨c₁, -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
      rw [tstep_capOp hterm trivial]
      refine ⟨by simp [evalOp], ?_⟩
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
      obtain ⟨n, j, Rf', h', hle⟩ := claim_presR hop hi hm (RLink_of hE.2.1 hE.2.2) hE.2.2
      refine ⟨n, j, Rf' + Rs, ⟨ρ, η, c₁, Rf', Rs, rfl, hE, ⟨he, hck⟩, OpT_TvOK hP hop htv, h', rfl,
        retPw_skel hPS hpw (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0)⟩, ?_⟩
      intro k
      have h1 := hle k
      simp only [Res.add_apply] at h1 ⊢
      omega

theorem CohR_subE {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} (hc : Coh η) (hr : CohR η) :
    CohR (subE ρ₀ η σs) := by
  have hE : CE (subE ρ₀ η σs) = CE η := rfl
  have hE' : CE (subE ρ₀ η σs).unsee = CE η.unsee := rfl
  intro k
  rw [hE, hE']
  cases hk : σs[k]? with
  | some σ =>
      rw [subE_wit_lt hk, subE_rrs_lt hk]
      have e : (subE ρ₀ η σs).urrs k = fun rt ws X => VRR ρ₀ η.unsee σ rt ws X := by simp only [subE, hk]
      refine ⟨fun ρ' S ws X => ?_, fun ρ' S ws X => ?_⟩
      · exact VRR_close hc hr ρ₀ σ [] 0 ρ₀ ρ' S ws X (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
      · rw [e]
        exact VRR_close hc.unsee hr.unsee ρ₀ σ [] 0 ρ₀ ρ' S ws X (fun _ => rfl)
          (fun _ h => absurd h (Nat.not_lt_zero _))
  | none =>
      have hl : σs.length ≤ k := by simpa using hk
      have e : (subE ρ₀ η σs).urrs k = η.urrs (k - σs.length) := by simp only [subE, hk]
      rw [subE_wit_ge hl, subE_rrs_ge hl, e]
      exact hr _

/-- Re-typing a value along `SubS` to the closed rendition of the supertype
(F2's `ret`, `enter`'s argument): shape and layout carry over. -/
theorem Lay_canon {cx : Cx} {σs : List Ty} {t τ rt : Ty} {ws : List Word} (hsub : SubS cx t τ)
    (hl : Lay σs t rt ws) : shp rt = shp (close σs τ) ∧ Lay σs τ (close σs τ) ws := by
  have hs : shp rt = shp (close σs τ) := by
    rw [shp_of_eskel hl.2.1]; exact shp_sub hsub σs 0 0
  have hw : wc rt = wc (close σs τ) := by
    rw [wc_of_eskel hl.2.1]; exact wc_sub hsub σs 0 0
  exact ⟨hs, ShapeC_wc hw hl.1, rfl, hw ▸ hl.2.2.1,
    Valid_sub hsub σs 0 0 ws (Valid_of_eskel hl.2.1 hl.2.2.2.1), rfl⟩

/-- **P1 + P4 at the thread, `ret`** into a caller frame. -/
theorem tstep_ret {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At}
    (hterm : th.term = .ret a) (hst : th.stack ≠ []) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | ret hu _ hsub =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      have hK := hi1.2.2.1 η (Ext_refl hE.2.1 hE.2.2) ws (by rw [← hs]; exact VR_sub hi1.1 hsub _ _ hv) hl'
      cases hstk : th.stack with
      | nil => exact absurd hstk hst
      | cons f rest =>
          rw [hstk] at hK
          obtain ⟨ρ', η', c, hCE, hE', hc, hvc, hf, hpwF⟩ := hK
          simp only [tstep, hterm, hstk, hea]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ', η', c, hCE, hE', hc, hvc, hf, hpwF⟩


theorem find_ok {p : Prog} {f : String} {d : Decl} (h : p.find f = .ok d) : p.find? (·.name == f) = some d := by
  unfold Prog.find at h
  split at h
  · rename_i d' hd; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hd
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### Counts and mentions under type shifts and substitution (moved from KindSound) -/

theorem info_top_shiftT : ∀ (t : Ty) (c : Nat), info Ty.top (t.shiftT c) = info Ty.top t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, info, iha c, ihb c]
  | sum a b iha ihb => intro c; simp only [Ty.shiftT, info, iha c, ihb c]
  | mu t ih => intro c; simp only [Ty.shiftT, info, top_cons, ih (c + 1)]
  | tex κ t ih => intro c; simp only [Ty.shiftT, info, top_cons, ih (c + 1)]
  | iall t ih => intro c; simp only [Ty.shiftT, info, top_shiftI, ih c]
  | iex t ih => intro c; simp only [Ty.shiftT, info, top_shiftI, ih c]
  | refine t ψ ih => intro c; simp only [Ty.shiftT, info, ih c]
  | tvar k => intro c; simp only [Ty.shiftT]; split <;> rfl
  | _ => intro c; rfl

theorem idxMentions_shiftT : ∀ (t : Ty) (c k : Nat), (t.shiftT c).idxMentions k = t.idxMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c k; simp only [Ty.shiftT, Ty.idxMentions, iha, ihb]
  | sum a b iha ihb => intro c k; simp only [Ty.shiftT, Ty.idxMentions, iha, ihb]
  | code a b iha ihb => intro c k; simp only [Ty.shiftT, Ty.idxMentions, iha, ihb]
  | array i t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | ptr μ t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | ptrOpt μ t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | loc μ t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | mu t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | tex κ t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | iall t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | iex t ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | refine t ψ ih => intro c k; simp only [Ty.shiftT, Ty.idxMentions, ih]
  | tvar j => intro c k; simp only [Ty.shiftT]; split <;> rfl
  | _ => intro c k; rfl

theorem tyMentions_shiftT : ∀ (t : Ty) (c k : Nat), k < c → (t.shiftT c).tyMentions k = t.tyMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, iha c k h, ihb c k h]
  | sum a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, iha c k h, ihb c k h]
  | code a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, iha c k h, ihb c k h]
  | array i t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | ptr μ t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | ptrOpt μ t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | loc μ t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | mu t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih (c + 1) (k + 1) (by omega)]
  | tex κ t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih (c + 1) (k + 1) (by omega)]
  | iall t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | iex t ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | refine t ψ ih => intro c k h; simp only [Ty.shiftT, Ty.tyMentions, ih c k h]
  | tvar j =>
      intro c k h
      simp only [Ty.shiftT]
      by_cases hj : j ≥ c
      · have h1 : j + 1 ≠ k := by omega
        have h2 : j ≠ k := by omega
        rw [if_pos hj]; simp only [Ty.tyMentions]; rw [beq_false_of_ne h1, beq_false_of_ne h2]
      · rw [if_neg hj]
  | _ => intro c k h; rfl

theorem countT_shiftT : ∀ (t : Ty) (c k : Nat), k < c → (t.shiftT c).countT k = t.countT k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c k h; simp only [Ty.shiftT, Ty.countT, iha c k h, ihb c k h]
  | refine t ψ ih => intro c k h; simp only [Ty.shiftT, Ty.countT, ih c k h]
  | iall t ih => intro c k h; simp only [Ty.shiftT, Ty.countT, ih c k h]
  | iex t ih => intro c k h; simp only [Ty.shiftT, Ty.countT, ih c k h]
  | tex κ t ih => intro c k h; simp only [Ty.shiftT, Ty.countT, ih (c + 1) (k + 1) (by omega)]
  | tvar j =>
      intro c k h
      by_cases hj : j ≥ c
      · have h1 : j + 1 ≠ k := by omega
        have h2 : j ≠ k := by omega
        simp [Ty.shiftT, hj, Ty.countT, Ty.tyMentions, h1, h2]
      · simp [Ty.shiftT, hj]
  | sum a b _ _ => intro c k h; have e := tyMentions_shiftT (.sum a b) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | code a b _ _ => intro c k h; have e := tyMentions_shiftT (.code a b) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | array i t _ => intro c k h; have e := tyMentions_shiftT (.array i t) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | ptr μ t _ => intro c k h; have e := tyMentions_shiftT (.ptr μ t) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | ptrOpt μ t _ => intro c k h; have e := tyMentions_shiftT (.ptrOpt μ t) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | loc μ t _ => intro c k h; have e := tyMentions_shiftT (.loc μ t) c k h; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countT, e]
  | mu t ih =>
      intro c k h
      simp only [Ty.shiftT, Ty.countT, ih (c + 1) (k + 1) (by omega), ih (c + 1) 0 (by omega),
        tyMentions_shiftT t (c + 1) (k + 1) (by omega)]
  | _ => intro c k h; rfl

theorem countI_shiftT : ∀ (t : Ty) (c k : Nat), (t.shiftT c).countI k = t.countI k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c k; simp only [Ty.shiftT, Ty.countI, iha, ihb]
  | refine t ψ ih => intro c k; simp only [Ty.shiftT, Ty.countI, ih]
  | iall t ih => intro c k; simp only [Ty.shiftT, Ty.countI, ih]
  | iex t ih => intro c k; simp only [Ty.shiftT, Ty.countI, ih]
  | tvar j => intro c k; simp only [Ty.shiftT]; split <;> rfl
  | sum a b _ _ => intro c k; have e := idxMentions_shiftT (.sum a b) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | code a b _ _ => intro c k; have e := idxMentions_shiftT (.code a b) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | array i t _ => intro c k; have e := idxMentions_shiftT (.array i t) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | ptr μ t _ => intro c k; have e := idxMentions_shiftT (.ptr μ t) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | ptrOpt μ t _ => intro c k; have e := idxMentions_shiftT (.ptrOpt μ t) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | loc μ t _ => intro c k; have e := idxMentions_shiftT (.loc μ t) c k; simp only [Ty.shiftT] at e ⊢; simp only [Ty.countI, e]
  | mu t ih =>
      intro c k
      simp only [Ty.shiftT, Ty.countI, ih, idxMentions_shiftT, countT_shiftT t (c + 1) 0 (by omega)]
  | tex κ t ih => intro c k; simp only [Ty.shiftT, Ty.countI, ih]
  | _ => intro c k; rfl

theorem width_shiftT (t : Ty) (c : Nat) : (t.shiftT c).width = t.width := by
  simp only [Ty.width, info_top_shiftT]

theorem tier_shiftT (t : Ty) (c : Nat) : (t.shiftT c).tier = t.tier := by
  simp only [Ty.tier, info_top_shiftT]

/-! ### Mentions under shifts and substitution -/

theorem idx_shift_self (c : Nat) : ∀ i : Idx, (i.shift c).mentions c = false
  | .lit _ => rfl
  | .var k => by
      by_cases h : k ≥ c
      · simp only [Idx.shift, h, if_true, Idx.mentions]; simp; omega
      · simp only [Idx.shift, h, if_false, Idx.mentions]; simp; omega
  | .add i j => by simp only [Idx.shift, Idx.mentions, idx_shift_self c i, idx_shift_self c j]; rfl
  | .sub i j => by simp only [Idx.shift, Idx.mentions, idx_shift_self c i, idx_shift_self c j]; rfl
  | .smul n i => by simp only [Idx.shift, Idx.mentions, idx_shift_self c i]

theorem idx_shift_succ (c k : Nat) (hk : k ≥ c) : ∀ i : Idx, (i.shift c).mentions (k + 1) = i.mentions k
  | .lit _ => rfl
  | .var j => by
      by_cases h : j ≥ c
      · simp only [Idx.shift, h, if_true, Idx.mentions]; simp
      · simp only [Idx.shift, h, if_false, Idx.mentions]
        rw [beq_false_of_ne (by omega), beq_false_of_ne (by omega)]
  | .add i j => by simp only [Idx.shift, Idx.mentions, idx_shift_succ c k hk i, idx_shift_succ c k hk j]
  | .sub i j => by simp only [Idx.shift, Idx.mentions, idx_shift_succ c k hk i, idx_shift_succ c k hk j]
  | .smul n i => by simp only [Idx.shift, Idx.mentions, idx_shift_succ c k hk i]

theorem pred_shift_self (c : Nat) : ∀ ψ : Pred, (ψ.shift c).mentions c = false
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.mentions, idx_shift_self]; rfl
  | .eq i j => by simp only [Pred.shift, Pred.mentions, idx_shift_self]; rfl
  | .and p q => by simp only [Pred.shift, Pred.mentions, pred_shift_self c p, pred_shift_self c q]; rfl
  | .ini i => by simp only [Pred.shift, Pred.mentions, idx_shift_self]

theorem pred_shift_succ (c k : Nat) (hk : k ≥ c) : ∀ ψ : Pred, (ψ.shift c).mentions (k + 1) = ψ.mentions k
  | .tt => rfl
  | .le i j => by simp only [Pred.shift, Pred.mentions, idx_shift_succ c k hk]
  | .eq i j => by simp only [Pred.shift, Pred.mentions, idx_shift_succ c k hk]
  | .and p q => by simp only [Pred.shift, Pred.mentions, pred_shift_succ c k hk p, pred_shift_succ c k hk q]
  | .ini i => by simp only [Pred.shift, Pred.mentions, idx_shift_succ c k hk]

theorem mode_shift_self (c : Nat) (μ : Mode) : (μ.shift c).mentions c = false := by
  cases μ <;> simp [Mode.shift, Mode.mentions, idx_shift_self]

theorem mode_shift_succ (c k : Nat) (hk : k ≥ c) (μ : Mode) : (μ.shift c).mentions (k + 1) = μ.mentions k := by
  cases μ <;> simp [Mode.shift, Mode.mentions, idx_shift_succ c k hk]

theorem ty_shiftI_self : ∀ (t : Ty) (c : Nat), (t.shiftI c).idxMentions c = false := by
  intro t
  induction t with
  | intS i => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | prod a b iha ihb => intro c; simp only [Ty.shiftI, Ty.idxMentions, iha, ihb]; rfl
  | sum a b iha ihb => intro c; simp only [Ty.shiftI, Ty.idxMentions, iha, ihb]; rfl
  | code a b iha ihb => intro c; simp only [Ty.shiftI, Ty.idxMentions, iha, ihb]; rfl
  | array i t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self, ih]; rfl
  | ptr μ t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_self, ih]; rfl
  | ptrOpt μ t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_self, ih]; rfl
  | loc μ t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_self, ih]; rfl
  | word r P => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | tok r i =>
      intro c
      rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | word2 r P => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | tok2 r P i j => intro c; simp [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | epair r P => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | tokE r P i => intro c; simp [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | share r => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | cap s r => intro c; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_self]
  | mu t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih]
  | tex κ t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih]
  | iall t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih]
  | iex t ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih]
  | refine t ψ ih => intro c; simp only [Ty.shiftI, Ty.idxMentions, ih, pred_shift_self]; rfl
  | _ => intro c; rfl

theorem ty_shiftI_succ : ∀ (t : Ty) (c k : Nat), k ≥ c → (t.shiftI c).idxMentions (k + 1) = t.idxMentions k := by
  intro t
  induction t with
  | intS i => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | prod a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | sum a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | code a b iha ihb => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, iha c k hk, ihb c k hk]
  | array i t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk, ih c k hk]
  | ptr μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_succ c k hk, ih c k hk]
  | ptrOpt μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_succ c k hk, ih c k hk]
  | loc μ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, mode_shift_succ c k hk, ih c k hk]
  | word r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | tok r i =>
      intro c k hk
      rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | word2 r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | tok2 r P i j => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | epair r P => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | tokE r P i => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | share r => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | cap s r => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, idx_shift_succ c k hk]
  | mu t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk]
  | tex κ t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk]
  | iall t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | iex t ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih (c + 1) (k + 1) (by omega)]
  | refine t ψ ih => intro c k hk; simp only [Ty.shiftI, Ty.idxMentions, ih c k hk, pred_shift_succ c k hk]
  | _ => intro c k hk; rfl

theorem idxMentions_subst (σs : List Ty) : ∀ (t : Ty) (c d k : Nat), k < d →
    (substTs σs c d t).idxMentions k = t.idxMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [substTs, Ty.idxMentions, iha c d k h, ihb c d k h]
  | sum a b iha ihb => intro c d k h; simp only [substTs, Ty.idxMentions, iha c d k h, ihb c d k h]
  | code a b iha ihb => intro c d k h; simp only [substTs, Ty.idxMentions, iha c d k h, ihb c d k h]
  | array i t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c d k h]
  | ptr μ t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c d k h]
  | ptrOpt μ t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c d k h]
  | loc μ t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c d k h]
  | mu t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih (c + 1) d k h]
  | tex κ t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih (c + 1) d k h]
  | iall t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c (d + 1) (k + 1) (by omega)]
  | iex t ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c (d + 1) (k + 1) (by omega)]
  | refine t ψ ih => intro c d k h; simp only [substTs, Ty.idxMentions, ih c d k h]
  | tvar j =>
      intro c d k h
      simp only [substTs]
      split
      · rfl
      · split
        · exact idxMentions_shiftIN d _ k h
        · rfl
  | _ => intro c d k h; rfl

theorem ty_shiftT_self : ∀ (t : Ty) (c : Nat), (t.shiftT c).tyMentions c = false := by
  intro t
  induction t with
  | tvar j =>
      intro c
      by_cases h : j ≥ c
      · have : j + 1 ≠ c := by omega
        rw [show (Ty.tvar j).shiftT c = .tvar (j + 1) by simp [Ty.shiftT, h]]
        simp only [Ty.tyMentions]; exact beq_false_of_ne this
      · have : j ≠ c := by omega
        rw [show (Ty.tvar j).shiftT c = .tvar j by simp [Ty.shiftT, h]]
        simp only [Ty.tyMentions]; exact beq_false_of_ne this
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, Ty.tyMentions, iha, ihb]; rfl
  | sum a b iha ihb => intro c; simp only [Ty.shiftT, Ty.tyMentions, iha, ihb]; rfl
  | code a b iha ihb => intro c; simp only [Ty.shiftT, Ty.tyMentions, iha, ihb]; rfl
  | array i t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | ptr μ t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | ptrOpt μ t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | loc μ t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | mu t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | tex κ t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | iall t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | iex t ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | refine t ψ ih => intro c; simp only [Ty.shiftT, Ty.tyMentions, ih]
  | _ => intro c; rfl

theorem ty_shiftT_succ : ∀ (t : Ty) (c k : Nat), k ≥ c → (t.shiftT c).tyMentions (k + 1) = t.tyMentions k := by
  intro t
  induction t with
  | tvar j =>
      intro c k hk
      by_cases h : j ≥ c
      · rw [show (Ty.tvar j).shiftT c = .tvar (j + 1) by simp [Ty.shiftT, h]]
        simp only [Ty.tyMentions]
        by_cases e : j = k
        · subst e; simp
        · rw [beq_false_of_ne e, beq_false_of_ne (by omega)]
      · rw [show (Ty.tvar j).shiftT c = .tvar j by simp [Ty.shiftT, h]]
        simp only [Ty.tyMentions]
        rw [beq_false_of_ne (by omega : j ≠ k + 1), beq_false_of_ne (by omega : j ≠ k)]
  | prod a b iha ihb => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, iha c k hk, ihb c k hk]
  | sum a b iha ihb => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, iha c k hk, ihb c k hk]
  | code a b iha ihb => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, iha c k hk, ihb c k hk]
  | array i t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | ptr μ t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | ptrOpt μ t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | loc μ t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | mu t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih (c + 1) (k + 1) (by omega)]
  | tex κ t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih (c + 1) (k + 1) (by omega)]
  | iall t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | iex t ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | refine t ψ ih => intro c k hk; simp only [Ty.shiftT, Ty.tyMentions, ih c k hk]
  | _ => intro c k hk; rfl

theorem tyMentions_shiftTN (X : Ty) : ∀ (c k : Nat), k < c → (shiftTN c X).tyMentions k = false
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | c + 1, 0, _ => ty_shiftT_self _ 0
  | c + 1, k + 1, h => by
      simp only [shiftTN]; rw [ty_shiftT_succ _ 0 k (Nat.zero_le k)]
      exact tyMentions_shiftTN X c k (by omega)

theorem tyMentions_shiftIN (X : Ty) (k : Nat) : ∀ d : Nat, (shiftIN d X).tyMentions k = X.tyMentions k
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, tyMentions_shiftI, tyMentions_shiftIN X k d]

theorem tyMentions_subst (σs : List Ty) : ∀ (t : Ty) (c d k : Nat), k < c →
    (substTs σs c d t).tyMentions k = t.tyMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [substTs, Ty.tyMentions, iha c d k h, ihb c d k h]
  | sum a b iha ihb => intro c d k h; simp only [substTs, Ty.tyMentions, iha c d k h, ihb c d k h]
  | code a b iha ihb => intro c d k h; simp only [substTs, Ty.tyMentions, iha c d k h, ihb c d k h]
  | array i t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c d k h]
  | ptr μ t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c d k h]
  | ptrOpt μ t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c d k h]
  | loc μ t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c d k h]
  | mu t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih (c + 1) d (k + 1) (by omega)]
  | tex κ t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih (c + 1) d (k + 1) (by omega)]
  | iall t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c (d + 1) k h]
  | iex t ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c (d + 1) k h]
  | refine t ψ ih => intro c d k h; simp only [substTs, Ty.tyMentions, ih c d k h]
  | tvar j =>
      intro c d k h
      simp only [substTs]
      by_cases hj : j < c
      · rw [if_pos hj]
      · rw [if_neg hj]
        split
        next _ σ hs =>
          rw [tyMentions_shiftIN, tyMentions_shiftTN _ c k h]
          simp only [Ty.tyMentions]; exact (beq_false_of_ne (by omega)).symm
        next _ hn =>
          have : σs.length ≤ j - c := List.getElem?_eq_none_iff.mp hn
          simp only [Ty.tyMentions]
          rw [beq_false_of_ne (by omega : j - σs.length ≠ k), beq_false_of_ne (by omega : j ≠ k)]
  | _ => intro c d k h; rfl

theorem countT_subst (σs : List Ty) : ∀ (t : Ty) (c d k : Nat), k < c →
    (substTs σs c d t).countT k = t.countT k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [substTs, Ty.countT, iha c d k h, ihb c d k h]
  | refine t ψ ih => intro c d k h; simp only [substTs, Ty.countT, ih c d k h]
  | iall t ih => intro c d k h; simp only [substTs, Ty.countT, ih c (d + 1) k h]
  | iex t ih => intro c d k h; simp only [substTs, Ty.countT, ih c (d + 1) k h]
  | tex κ t ih => intro c d k h; simp only [substTs, Ty.countT, ih (c + 1) d (k + 1) (by omega)]
  | tvar j =>
      intro c d k h
      simp only [substTs]
      by_cases hj : j < c
      · rw [if_pos hj]
      · rw [if_neg hj]
        split
        next _ σ hs =>
          rw [countT_zero _ k (by rw [tyMentions_shiftIN, tyMentions_shiftTN _ c k h])]
          have e1 : Ty.tyMentions k (.tvar j) = false := by
            simp only [Ty.tyMentions]; exact beq_false_of_ne (by omega)
          simp [Ty.countT, e1]
        next _ hn =>
          have : σs.length ≤ j - c := List.getElem?_eq_none_iff.mp hn
          have e1 : Ty.tyMentions k (.tvar j) = false := by
            simp only [Ty.tyMentions]; exact beq_false_of_ne (by omega)
          have e2 : Ty.tyMentions k (.tvar (j - σs.length)) = false := by
            simp only [Ty.tyMentions]; exact beq_false_of_ne (by omega)
          simp [Ty.countT, e1, e2]
  | sum a b _ _ => intro c d k h; have e := tyMentions_subst σs (.sum a b) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | code a b _ _ => intro c d k h; have e := tyMentions_subst σs (.code a b) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | array i t _ => intro c d k h; have e := tyMentions_subst σs (.array i t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | ptr μ t _ => intro c d k h; have e := tyMentions_subst σs (.ptr μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | ptrOpt μ t _ => intro c d k h; have e := tyMentions_subst σs (.ptrOpt μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | loc μ t _ => intro c d k h; have e := tyMentions_subst σs (.loc μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countT, e]
  | mu t ih =>
      intro c d k h
      simp only [substTs, Ty.countT, ih (c + 1) d (k + 1) (by omega), ih (c + 1) d 0 (by omega),
        tyMentions_subst σs t (c + 1) d (k + 1) (by omega)]
  | _ => intro c d k h; rfl

theorem countI_subst (σs : List Ty) : ∀ (t : Ty) (c d k : Nat), k < d →
    (substTs σs c d t).countI k = t.countI k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [substTs, Ty.countI, iha c d k h, ihb c d k h]
  | refine t ψ ih => intro c d k h; simp only [substTs, Ty.countI, ih c d k h]
  | iall t ih => intro c d k h; simp only [substTs, Ty.countI, ih c (d + 1) (k + 1) (by omega)]
  | iex t ih => intro c d k h; simp only [substTs, Ty.countI, ih c (d + 1) (k + 1) (by omega)]
  | tvar j =>
      intro c d k h
      simp only [substTs]
      split
      · rfl
      · split
        · rw [countI_zero _ k (idxMentions_shiftIN d _ k h)]; rfl
        · rfl
  | sum a b _ _ => intro c d k h; have e := idxMentions_subst σs (.sum a b) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | code a b _ _ => intro c d k h; have e := idxMentions_subst σs (.code a b) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | array i t _ => intro c d k h; have e := idxMentions_subst σs (.array i t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | ptr μ t _ => intro c d k h; have e := idxMentions_subst σs (.ptr μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | ptrOpt μ t _ => intro c d k h; have e := idxMentions_subst σs (.ptrOpt μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | loc μ t _ => intro c d k h; have e := idxMentions_subst σs (.loc μ t) c d k h; simp only [substTs] at e ⊢; simp only [Ty.countI, e]
  | mu t ih =>
      intro c d k h
      simp only [substTs, Ty.countI, ih (c + 1) d k h, idxMentions_subst σs t (c + 1) d k h,
        countT_subst σs t (c + 1) d 0 (by omega)]
  | tex κ t ih => intro c d k h; simp only [substTs, Ty.countI, ih (c + 1) d k h]
  | _ => intro c d k h; rfl

/-! ### Layout agreement of `close σs` and `cl ρ W` (T3c-5c L3) -/

section AccsCl
open CoupledCl

theorem clI_mentions_eq (ρ : Nat → Nat) (d k : Nat) (hk : k < d) : ∀ i : Idx,
    (clI ρ d i).mentions k = i.mentions k
  | .lit n => rfl
  | .var j => by
      by_cases h : j < d
      · simp only [clI, h, ↓reduceIte]
      · simp only [clI, h, ↓reduceIte, Idx.mentions]
        exact (beq_false_of_ne (by omega)).symm
  | .add i j => by
      simp only [clI, addF_mentions, Idx.mentions, clI_mentions_eq ρ d k hk i, clI_mentions_eq ρ d k hk j]
  | .sub i j => by
      simp only [clI, subF_mentions, Idx.mentions, clI_mentions_eq ρ d k hk i, clI_mentions_eq ρ d k hk j]
  | .smul n i => by simp only [clI, smulF_mentions, Idx.mentions, clI_mentions_eq ρ d k hk i]

theorem clM_mentions_eq (ρ : Nat → Nat) (d k : Nat) (hk : k < d) (μ : Mode) :
    (clM ρ d μ).mentions k = μ.mentions k := by
  cases μ <;> simp only [clM, Mode.mentions, clI_mentions_eq ρ d k hk]

theorem clP_mentions_eq (ρ : Nat → Nat) (d k : Nat) (hk : k < d) : ∀ ψ : Pred,
    (clP ρ d ψ).mentions k = ψ.mentions k
  | .tt => rfl
  | .le i j => by simp only [clP, Pred.mentions, clI_mentions_eq ρ d k hk]
  | .eq i j => by simp only [clP, Pred.mentions, clI_mentions_eq ρ d k hk]
  | .and p q => by simp only [clP, Pred.mentions, clP_mentions_eq ρ d k hk p, clP_mentions_eq ρ d k hk q]
  | .ini i => by simp only [clP, Pred.mentions, clI_mentions_eq ρ d k hk]

/-- A closure keeps exactly the bound index mentions. -/
theorem idxMentions_cl_eq (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).idxMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < d → (cl ρ W c d t).idxMentions k = t.idxMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.idxMentions, iha c d k h, ihb c d k h]
  | sum a b iha ihb => intro c d k h; simp only [cl, Ty.idxMentions, iha c d k h, ihb c d k h]
  | code a b iha ihb => intro c d k h; simp only [cl, Ty.idxMentions, iha c d k h, ihb c d k h]
  | array i t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c d k h, clI_mentions_eq ρ d k h]
  | ptr μ t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c d k h, clM_mentions_eq ρ d k h]
  | ptrOpt μ t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c d k h, clM_mentions_eq ρ d k h]
  | loc μ t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c d k h, clM_mentions_eq ρ d k h]
  | refine t ψ ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c d k h, clP_mentions_eq ρ d k h]
  | mu t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih (c + 1) d k h]
  | tex κ t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih (c + 1) d k h]
  | iall t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c (d + 1) (k + 1) (by omega)]
  | iex t ih => intro c d k h; simp only [cl, Ty.idxMentions, ih c (d + 1) (k + 1) (by omega)]
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp only [cl, hj, ↓reduceIte]
      · simp only [cl, hj, ↓reduceIte, hW, Ty.idxMentions]
  | intS i => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | word r P => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | word2 r P => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | tok2 r P i j => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | epair r P => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | tokE r P i => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | share r => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | cap s r => intro c d k h; simp only [cl, Ty.idxMentions, clI_mentions_eq ρ d k h]
  | tok r st =>
      intro c d k h
      rcases st with _ | ⟨P, i⟩ <;>
        simp [cl, Ty.idxMentions, Option.map, Option.any, clI_mentions_eq ρ d k h]
  | _ => intro c d k h; rfl

/-- A closure keeps exactly the bound type mentions. -/
theorem tyMentions_cl_eq (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).tyMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < c → (cl ρ W c d t).tyMentions k = t.tyMentions k := by
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.tyMentions, iha c d k h, ihb c d k h]
  | sum a b iha ihb => intro c d k h; simp only [cl, Ty.tyMentions, iha c d k h, ihb c d k h]
  | code a b iha ihb => intro c d k h; simp only [cl, Ty.tyMentions, iha c d k h, ihb c d k h]
  | array i t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c d k h]
  | ptr μ t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c d k h]
  | ptrOpt μ t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c d k h]
  | loc μ t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c d k h]
  | refine t ψ ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c d k h]
  | iall t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c (d + 1) k h]
  | iex t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih c (d + 1) k h]
  | mu t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih (c + 1) d (k + 1) (by omega)]
  | tex κ t ih => intro c d k h; simp only [cl, Ty.tyMentions, ih (c + 1) d (k + 1) (by omega)]
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp only [cl, hj, ↓reduceIte]
      · simp only [cl, hj, ↓reduceIte, hW, Ty.tyMentions]
        exact (beq_false_of_ne (by omega)).symm
  | _ => intro c d k h; simp [cl, Ty.tyMentions]

theorem countT_cl_eq (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j m, (W j).tyMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < c → (cl ρ W c d t).countT k = t.countT k := by
  have hm := tyMentions_cl_eq ρ W hW
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.countT, iha c d k h, ihb c d k h]
  | refine t ψ ih => intro c d k h; simp only [cl, Ty.countT, ih c d k h]
  | iall t ih => intro c d k h; simp only [cl, Ty.countT, ih c (d + 1) k h]
  | iex t ih => intro c d k h; simp only [cl, Ty.countT, ih c (d + 1) k h]
  | tex κ t ih => intro c d k h; simp only [cl, Ty.countT, ih (c + 1) d (k + 1) (by omega)]
  | mu t ih =>
      intro c d k h
      simp only [cl, Ty.countT, ih (c + 1) d (k + 1) (by omega), ih (c + 1) d 0 (by omega),
        hm t (c + 1) d (k + 1) (by omega)]
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp only [cl, hj, ↓reduceIte]
      · simp only [cl, hj, ↓reduceIte]
        rw [countT_zero _ k (hW _ _), countT_zero _ k (by simp only [Ty.tyMentions]; exact beq_false_of_ne (by omega))]
  | sum a b _ _ => intro c d k h; have e := hm (.sum a b) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | code a b _ _ => intro c d k h; have e := hm (.code a b) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | array i t _ => intro c d k h; have e := hm (.array i t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | ptr μ t _ => intro c d k h; have e := hm (.ptr μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | ptrOpt μ t _ => intro c d k h; have e := hm (.ptrOpt μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | loc μ t _ => intro c d k h; have e := hm (.loc μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countT, e]
  | _ => intro c d k h; simp [cl, Ty.countT, Ty.tyMentions]

theorem countI_cl_eq (ρ : Nat → Nat) (W : Nat → Ty) (hWT : ∀ j m, (W j).tyMentions m = false)
    (hWI : ∀ j m, (W j).idxMentions m = false) :
    ∀ (t : Ty) (c d k : Nat), k < d → (cl ρ W c d t).countI k = t.countI k := by
  have hm := idxMentions_cl_eq ρ W hWI
  intro t
  induction t with
  | prod a b iha ihb => intro c d k h; simp only [cl, Ty.countI, iha c d k h, ihb c d k h]
  | refine t ψ ih => intro c d k h; simp only [cl, Ty.countI, ih c d k h, clP_mentions_eq ρ d k h]
  | iall t ih => intro c d k h; simp only [cl, Ty.countI, ih c (d + 1) (k + 1) (by omega)]
  | iex t ih => intro c d k h; simp only [cl, Ty.countI, ih c (d + 1) (k + 1) (by omega)]
  | tex κ t ih => intro c d k h; simp only [cl, Ty.countI, ih (c + 1) d k h]
  | mu t ih =>
      intro c d k h
      simp only [cl, Ty.countI, ih (c + 1) d k h, countT_cl_eq ρ W hWT t (c + 1) d 0 (by omega),
        hm t (c + 1) d k h]
  | tvar j =>
      intro c d k h
      by_cases hj : j < c
      · simp only [cl, hj, ↓reduceIte]
      · simp only [cl, hj, ↓reduceIte]
        rw [countI_zero _ k (hWI _ _), countI_zero _ k rfl]
  | intS i => intro c d k h; have e := hm (.intS i) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | word r P => intro c d k h; have e := hm (.word r P) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | tok r st => intro c d k h; have e := hm (.tok r st) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | word2 r P => intro c d k h; have e := hm (.word2 r P) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | tok2 r P i j => intro c d k h; have e := hm (.tok2 r P i j) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | epair r P => intro c d k h; have e := hm (.epair r P) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | tokE r P i => intro c d k h; have e := hm (.tokE r P i) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | share r => intro c d k h; have e := hm (.share r) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | cap s r => intro c d k h; have e := hm (.cap s r) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | sum a b _ _ => intro c d k h; have e := hm (.sum a b) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | code a b _ _ => intro c d k h; have e := hm (.code a b) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | array i t _ => intro c d k h; have e := hm (.array i t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | ptr μ t _ => intro c d k h; have e := hm (.ptr μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | ptrOpt μ t _ => intro c d k h; have e := hm (.ptrOpt μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | loc μ t _ => intro c d k h; have e := hm (.loc μ t) c d k h; simp only [cl] at e ⊢; simp only [Ty.countI, e]
  | _ => intro c d k h; rfl

theorem info_sig (t : Ty) : info Ty.top (sig t) = info Ty.top t := by
  simp only [sig, info_er _ Ty.top (fun _ => rfl), info_skel]

theorem rawWords_of_sig {a b : Ty} (h : sig a = sig b) : a.rawWords = b.rawWords := by
  simp only [Ty.rawWords, Ty.width]; rw [← info_sig a, ← info_sig b, h]

theorem tier_of_sig {a b : Ty} (h : sig a = sig b) : a.tier = b.tier := by
  simp only [Ty.tier]; rw [← info_sig a, ← info_sig b, h]

theorem rawWords_shiftT (t : Ty) (c : Nat) : (t.shiftT c).rawWords = t.rawWords := by
  simp only [Ty.rawWords, width_shiftT]

/-- **Type shifts do not move layouts.** -/
theorem accs_shiftT : ∀ (t : Ty) (c : Nat), accs (t.shiftT c) = accs t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp only [Ty.shiftT, accs, iha c, ihb c]
  | refine t ψ ih => intro c; simp only [Ty.shiftT, accs, ih c]
  | iall t ih => intro c; simp only [Ty.shiftT, accs, ih c]
  | mu t ih => intro c; simp only [Ty.shiftT, accs, ih (c + 1)]
  | iex t ih =>
      intro c
      have hr := rawWords_shiftT (.iex t) c
      simp only [Ty.shiftT] at hr
      simp only [Ty.shiftT, accs, countI_shiftT t c 0, hr, ih c]
  | tex κ t ih =>
      intro c
      have hr := rawWords_shiftT (.tex κ t) c
      simp only [Ty.shiftT] at hr
      simp only [Ty.shiftT, accs, countT_shiftT t (c + 1) 0 (by omega), hr, ih (c + 1)]
  | sum a b _ _ =>
      intro c
      have ht := tier_shiftT (.sum a b) c
      simp only [Ty.shiftT] at ht
      simp only [Ty.shiftT, accs, ht]
  | tvar j => intro c; simp only [Ty.shiftT]; split <;> rfl
  | _ => intro c; rfl

theorem accs_shiftTN : ∀ (n : Nat) (t : Ty), accs (shiftTN n t) = accs t
  | 0, _ => rfl
  | n + 1, t => by simp only [shiftTN, accs_shiftT, accs_shiftTN n t]

theorem accs_substTs_tvar (σs : List Ty) (c d k : Nat) :
    accs (substTs σs c d (.tvar (c + k))) = accs (close σs (.tvar k)) := by
  have h1 : ¬ c + k < c := by omega
  have h2 : c + k - c = k := by omega
  simp only [close, substTs, h1, h2, ite_false, Nat.not_lt_zero, Nat.sub_zero]
  cases σs[k]? with
  | none => rfl
  | some σ => simp only [accs_shiftIN, accs_shiftTN]

/-- **Layout agreement of the two renditions**: where every unguarded type
variable agrees in `sig` and in layout, `close σs t` and `cl ρ W 0 0 t` have
the same accesses.  Coupling (`countI`/`countT` of a package's bound index)
is the same in both: substitution and closure keep bound mentions. -/
theorem accs_cl_close (σs : List Ty) (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ k, Clo (W k)) :
    ∀ (t : Ty) (c d : Nat),
      (∀ k, t.guardT (c + k) = false → sig (close σs (.tvar k)) = sig (W k)) →
      (∀ k, t.guardT (c + k) = false → accs (close σs (.tvar k)) = accs (W k)) →
      accs (substTs σs c d t) = accs (cl ρ W c d t) := by
  have hWT : ∀ j m, (W j).tyMentions m = false := fun j m => Clo_tyMentions (hW j) m
  have hWI : ∀ j m, (W j).idxMentions m = false := fun j m => Clo_idxMentions (hW j) m
  intro t
  induction t with
  | tvar j =>
      intro c d _ HA
      by_cases hj : j < c
      · simp [substTs, cl, hj, accs]
      · obtain ⟨k, rfl⟩ : ∃ k, j = c + k := ⟨j - c, by omega⟩
        rw [accs_substTs_tvar, HA k (by simp [Ty.guardT])]
        have e : c + k - c = k := by omega
        simp only [cl, hj, e, ite_false]
  | prod a b iha ihb =>
      intro c d HS HA
      have e1 := iha c d (fun k hk => HS k (by simp [Ty.guardT, hk])) (fun k hk => HA k (by simp [Ty.guardT, hk]))
      have e2 := ihb c d (fun k hk => HS k (by simp [Ty.guardT, hk])) (fun k hk => HA k (by simp [Ty.guardT, hk]))
      simp only [substTs, cl, accs, e1, e2]
  | sum a b _ _ =>
      intro c d HS _
      have e := tier_of_sig (sig_close_cl σs ρ W (.sum a b) c d HS)
      simp only [substTs, cl] at e ⊢
      simp only [accs, e]
  | mu t ih =>
      intro c d HS HA
      have e1 := ih (c + 1) d
        (fun k hk => HS k (by
          have e : c + 1 + k = c + k + 1 := by omega
          rw [e] at hk; simpa [Ty.guardT] using hk))
        (fun k hk => HA k (by
          have e : c + 1 + k = c + k + 1 := by omega
          rw [e] at hk; simpa [Ty.guardT] using hk))
      simp only [substTs, cl, accs, e1]
  | tex κ t ih =>
      intro c d HS HA
      have e1 := ih (c + 1) d
        (fun k hk => HS k (by
          have e : c + 1 + k = c + k + 1 := by omega
          rw [e] at hk; simpa [Ty.guardT] using hk))
        (fun k hk => HA k (by
          have e : c + 1 + k = c + k + 1 := by omega
          rw [e] at hk; simpa [Ty.guardT] using hk))
      have er := rawWords_of_sig (sig_close_cl σs ρ W (.tex κ t) c d HS)
      simp only [substTs, cl] at er ⊢
      simp only [accs, e1, er, countT_subst σs t (c + 1) d 0 (by omega),
        countT_cl_eq ρ W hWT t (c + 1) d 0 (by omega)]
  | iall t ih =>
      intro c d HS HA
      have e1 := ih c (d + 1) (fun k hk => HS k (by simpa [Ty.guardT] using hk))
        (fun k hk => HA k (by simpa [Ty.guardT] using hk))
      simp only [substTs, cl, accs, e1]
  | iex t ih =>
      intro c d HS HA
      have e1 := ih c (d + 1) (fun k hk => HS k (by simpa [Ty.guardT] using hk))
        (fun k hk => HA k (by simpa [Ty.guardT] using hk))
      have er := rawWords_of_sig (sig_close_cl σs ρ W (.iex t) c d HS)
      simp only [substTs, cl] at er ⊢
      simp only [accs, e1, er, countI_subst σs t c (d + 1) 0 (by omega),
        countI_cl_eq ρ W hWT hWI t c (d + 1) 0 (by omega)]
  | refine t ψ ih =>
      intro c d HS HA
      have e1 := ih c d (fun k hk => HS k (by simpa [Ty.guardT] using hk))
        (fun k hk => HA k (by simpa [Ty.guardT] using hk))
      simp only [substTs, cl, accs, e1]
  | _ => intro c d _ _; simp [substTs, cl, accs]

/-- `accs` counterpart of `sig_WitL`. -/
theorem accs_WitL {σs : List Ty} {W : Nat → Ty} {opq : List Nat} (h : WitL σs W opq)
    (hC : ∀ k, Clo (W k)) (ρ : Nat → Nat) {t : Ty} (hg : opq.all (fun k => t.guardT k) = true)
    (hr : ∀ k, t.guardT k = false → k < σs.length) : accs (close σs t) = accs (cl ρ W 0 0 t) := by
  refine accs_cl_close σs ρ W hC t 0 0 (fun k hk => ?_) (fun k hk => ?_)
  · simp only [Nat.zero_add] at hk
    refine h.1 k (fun hm => ?_) (hr k hk)
    have := List.all_eq_true.1 hg k hm
    rw [hk] at this; cases this
  · simp only [Nat.zero_add] at hk
    refine h.2.2 k (fun hm => ?_) (hr k hk)
    have := List.all_eq_true.1 hg k hm
    rw [hk] at this; cases this

end AccsCl

/-- **The callee's layout agreement**: its type arguments are the caller's
closed at both renditions, and each is `opaqueOK` and well formed. -/
theorem WitL_call {σs ts : List Ty} {η : TEnv} {ρ : Nat → Nat} {cx : Cx} (hW : WitL σs η.wit cx.opq)
    (hK : cx.ke.length ≤ σs.length) (hC : ∀ k, Clo (η.wit k))
    (hts : ∀ σ ∈ ts, cx.opaqueOK σ = true ∧ σ.wf cx.ke.length cx.inames.length = true) :
    WitL (ts.map (close σs)).reverse (subE ρ η ts.reverse).wit [] := by
  have hr : ∀ σ ∈ ts, ∀ j, σ.guardT j = false → j < σs.length := fun σ hm j hj =>
    Nat.lt_of_not_le (fun hc => by
      have := guardT_of_wf σ _ _ j (hts σ hm).2 (Nat.le_trans hK hc)
      rw [hj] at this; cases this)
  refine ⟨fun k _ hk => ?_, fun k σ' hσ' => ⟨fun _ => ?_, fun h => by cases h⟩, fun k _ hk => ?_⟩
  rotate_left
  · rw [← List.map_reverse, List.getElem?_map] at hσ'
    cases hσ : ts.reverse[k]? with
    | none => simp [hσ] at hσ'
    | some σ =>
        simp only [hσ, Option.map_some, Option.some.injEq] at hσ'
        subst hσ'
        rw [subE_wit_lt hσ]
        have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
        exact zrel_WitL hW hC ρ (hts σ hmem).1 (hr σ hmem)
  · have hk' : k < ts.reverse.length := by simpa using hk
    have hσ : ts.reverse[k]? = some (ts.reverse[k]'hk') := List.getElem?_eq_getElem hk'
    generalize ts.reverse[k]'hk' = σ at hσ
    have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
    obtain ⟨ho, hwf⟩ := hts σ hmem
    have e1 : ((ts.map (close σs)).reverse)[k]? = some (close σs σ) := by
      rw [← List.map_reverse, List.getElem?_map, hσ]; rfl
    have e2 : accs (close (ts.map (close σs)).reverse (.tvar k)) = accs (close σs σ) := by
      show accs (substTs _ 0 0 (.tvar k)) = _
      simp only [substTs, Nat.not_lt_zero, if_false, ite_false, Nat.sub_zero, e1, accs_shiftIN, accs_shiftTN]
    rw [e2, subE_wit_lt hσ]
    refine accs_WitL hW hC ρ ho (fun j hj => Nat.lt_of_not_le (fun hc => ?_))
    have := guardT_of_wf σ _ _ j hwf (Nat.le_trans hK hc)
    rw [hj] at this; cases this
  have hk' : k < ts.reverse.length := by simpa using hk
  have hσ : ts.reverse[k]? = some (ts.reverse[k]'hk') := List.getElem?_eq_getElem hk'
  generalize ts.reverse[k]'hk' = σ at hσ
  have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
  obtain ⟨ho, hwf⟩ := hts σ hmem
  have e1 : ((ts.map (close σs)).reverse)[k]? = some (close σs σ) := by
    rw [← List.map_reverse, List.getElem?_map, hσ]; rfl
  have e2 : sig (close (ts.map (close σs)).reverse (.tvar k)) = sig (close σs σ) := by
    show sig (substTs _ 0 0 (.tvar k)) = _
    simp only [substTs, Nat.not_lt_zero, if_false, ite_false, Nat.sub_zero, e1, sig_shiftIN, sig_shiftTN]
  rw [e2, subE_wit_lt hσ]
  refine sig_WitL hW ρ ho (fun j hj => Nat.lt_of_not_le (fun hc => ?_))
  have := guardT_of_wf σ _ _ j hwf (Nat.le_trans hK hc)
  rw [hj] at this; cases this

theorem admitsIn_zero {cx : Cx} {κ : Kind} {σ : Ty} (h : admitsIn cx κ σ = true) (e : κ.zero = true) :
    zeroableIn [] cx.ke σ = true := by
  simp only [admitsIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hz⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  simpa [e] using hz

/-- (T3c-5a) The callee's witnesses are the caller's closures of admitted type
arguments: no by-value array. -/
theorem WitAF_subE {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} (hw : WitAF η)
    (hs : ∀ σ ∈ σs, σ.arrFree = true) (hn : ∀ σ ∈ σs, noIallV σ = true)
    (hC : ∀ k, Clo (η.wit k)) (hm : ∀ σ ∈ σs, TermTv.mg σ = true) : WitAF (subE ρ₀ η σs) := by
  intro k
  show (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)).arrFree = true ∧
    noIallV (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)) = true ∧
    TermTv.mg (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)) = true
  split
  · rename_i σ h
    exact ⟨arrFree_cl hw.af σ 0 0 (hs σ (List.mem_of_getElem? h)), noIallV_cl hw.ni σ 0 0 (hn σ (List.mem_of_getElem? h)),
      TermTv.mg_cl (fun k => (hC k).1) hw.mg σ 0 0 (hm σ (List.mem_of_getElem? h))⟩
  · exact hw _

theorem WitSh_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitSh cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitSh (d.tparams.reverse.map some) (subE ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hsh : κ.share = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.coupledOK (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact coupledOK_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) (admitsIn_share had hsh)
      (tb_of_wf σ (admitsIn_wf had))

theorem WitC_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitC cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitC (d.tparams.reverse.map some) (subE ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hcp : κ.copy = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.affine (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = false
    rw [e]
    exact AffineCl.affine_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) σ ((admitsIn_word had).2 hcp)
      (tb_of_wf σ (admitsIn_wf had))

theorem WitN_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitN cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitN (d.tparams.reverse.map some) (subE ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hno : κ.noOwn = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.noOwn (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact NoOwnCl.noOwn_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) σ (admitsIn_noOwn had hno)
      (tb_of_wf σ (admitsIn_wf had))

/-- (S7) The callee's `share` witnesses are region-free: the caller's closures
of `share`-admitted (so `coupledOKIn`), region-free type arguments (the scope's
check at the call, until R2). -/
theorem WitR_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hS : WitR cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true) :
    WitR (d.tparams.reverse.map some) (subE ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hsh : κ.share = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show rgnFree (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact rgnFree_cl0 ρ₀ η.wit cx.ke hS (admitsIn_share had hsh) (hrt σ (List.mem_of_getElem? hσ))

theorem instantiate_arrFree {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (hinst : instantiate cx d is ts = .ok (at_, rt)) : ∀ σ ∈ ts.reverse, σ.arrFree = true := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro σ hσ
  rw [List.mem_reverse] at hσ
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hσ
  have hz : j < (d.tparams.zip ts).length := by simp [List.length_zip]; omega
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  exact admitsIn_arrFree (ha _ _ hm)

theorem instantiate_wf {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    ∀ σ ∈ ts.reverse, σ.wf cx.ke.length cx.inames.length = true := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro σ hσ
  rw [List.mem_reverse] at hσ
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hσ
  have hz : j < (d.tparams.zip ts).length := by simp [List.length_zip]; omega
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  exact admitsIn_wf (ha _ _ hm)

/-- **The callee's type arguments respect its kinds**: `instantiate` checked
`admitsIn`, and the caller's own arguments respect the caller's kinds. -/
theorem KindsOK_call {σs ts : List Ty} {cx : Cx} {d : Decl} {is : List String} {at_ rt : Ty}
    (hZ : ZeroCloseP) (hK : KindsOK cx.ke σs) (hlen : cx.ke.length ≤ σs.length)
    (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    KindsOK (d.tparams.reverse.map some) (ts.map (close σs)).reverse := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  -- the argument at callee variable `k`, and its kind
  have arg : ∀ (k : Nat) (κ : Kind), (d.tparams.reverse.map some : KEnv)[k]? = some (some κ) →
      ∃ σ, ((ts.map (close σs)).reverse)[k]? = some (close σs σ) ∧ admitsIn cx κ σ = true := by
    intro k κ hk
    rw [List.getElem?_map] at hk
    cases hκ : d.tparams.reverse[k]? with
    | none => simp [hκ] at hk
    | some κ' =>
      simp only [hκ, Option.map_some, Option.some.injEq] at hk
      subst hk
      have hkl : k < d.tparams.length := by
        have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
      rw [List.getElem?_reverse hkl] at hκ
      have hj : d.tparams.length - 1 - k < ts.length := by omega
      have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
        List.getElem?_eq_getElem hj
      generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
      have hm : (κ', σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
      have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
      exact ⟨σ, by rw [← List.map_reverse, List.getElem?_map, e]; rfl, ha κ' σ hm⟩
  have kl : KindsL (ts.map (close σs)).reverse := by
    intro σ' h
    rw [← List.map_reverse, List.mem_map] at h
    obtain ⟨σ, hσ, rfl⟩ := h
    exact accs_close (instantiate_wf hinst σ hσ) hlen (instantiate_arrFree hinst σ hσ) hK.2.2
  refine ⟨fun k hk => ?_, fun k hk => ?_, kl⟩
  rotate_left
  · unfold KEnv.ask at hk
    split at hk
    · rename_i κ hκ
      obtain ⟨σ, e, hadm⟩ := arg k κ hκ
      exact ⟨close σs σ, e, hZ cx.ke σs σ hK.2.1 (admitsIn_zero hadm hk)⟩
    · cases hk
    · cases hk
  unfold KEnv.ask at hk
  rw [List.getElem?_map] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => simp [hκ] at hk
  | some κ =>
    simp only [hκ, Option.map_some] at hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    refine ⟨close σs σ, by rw [← List.map_reverse, List.getElem?_map, e]; rfl, ?_⟩
    obtain ⟨hw, hc⟩ := admitsIn_word (ha κ σ hm)
    cases hn : κ.noWord
    · simp only [hn, Bool.false_or] at hk
      exact wordFree_close hK σ (wordFreeIn_of_affine σ (hc hk))
    · exact wordFree_close hK σ (hw hn)

/-- Re-type laid-out words to another closed rendition with the same skeleton. -/
theorem Lay_move {σ1 σ2 : List Ty} {t1 t2 T : Ty} {ws : List Word} (hl : Lay σ1 t1 T ws)
    (e : skel T = skel (close σ2 t2)) : Lay σ2 t2 (close σ2 t2) ws :=
  ⟨ShapeC_wc (wc_of_skel e) hl.1, rfl, wc_of_skel e ▸ hl.2.2.1, Valid_of_skel e hl.2.2.2.1, rfl⟩

/-- Re-type laid-out words to another closed rendition with the same `sig`
(a closure's argument, 24e). -/
theorem Lay_move_sig {σ1 σ2 : List Ty} {t1 t2 T : Ty} {ws : List Word} (hl : Lay σ1 t1 T ws)
    (e : sig T = sig (close σ2 t2)) : Lay σ2 t2 (close σ2 t2) ws :=
  ⟨ShapeC_wc (wc_of_sig e) hl.1, rfl, wc_of_sig e ▸ hl.2.2.1, Valid_of_sig e hl.2.2.2.1, rfl⟩

theorem Sat_nil (ρ : Nat → Nat) : Sat [] ρ := by intro k t h; simp at h

/-- **P1 + P4 at the thread, `call`.**  The callee's frame is typed at the
declaration's context with `ρ` extended by the index arguments and `η` the
caller's `VR` at the type arguments (row 18); the pushed frame resumes the
caller at the instantiated return type. -/
theorem tstep_call {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.call f is a ts) e) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPw th.σs th.stack cx.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @call _ _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hb =>
          obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
          have hd := find_ok hfind
          have hDT := hP d (List.mem_of_find?_eq_some hd)
          have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInv hu hi
          have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
          have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
          have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, callFrame, enter, hp, hd, hea, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subE ρ η ts.reverse, declCx d, rfl, ⟨hE.1, Coh_subE hE.2.1, CohR_subE hE.2.1 hE.2.2⟩, hbody, declCx_TvOK hDT hRI,
            ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun f rest h ws => by injection h with h1 h2; subst h1; rfl⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : d.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
              rw [← shp_of_skel Ea, ← hs]
              exact (VR_call ts us η ρ d.argTy _ ws).1 (VR_sub hi1.1 hsub _ _ hv)
            · simp at hen
          · intro η' hx ws' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_back (η₁ := subE ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hv'' := (VR_coh (Coh_subE h2.1) hx.1 hx.2.1.symm hC _ _ _ _).2 hv'
            refine ⟨ρ, η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC, ⟨hE.1, h2.1, h2.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
              bind_FInv hb (FInv_ext hE.2.1 h2 hi1) ((VR_call ts us _ ρ d.retTy _ ws').2 hv'') ?_, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws⟩
            exact ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
          · exact WitL_call hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
          · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.2.2.2.2.2.1 hi.2.2.2.2.1 hinst,
              WitAF_subE hi.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
              WitSh_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.1 hinst,
              WitC_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.1 hinst,
              WitN_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.2.1 hinst,
              WitR_call hi.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩

/-- **P1 + P4 at the thread, `tail`.**  No frame is pushed: the callee returns
straight into the current frame's continuation, via `SubS rt c₁.ret`. -/
theorem tstep_tail {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {f : String} {is : List String} {a : At} {ts : List Ty}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .tail f is a ts) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | @tail _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hsubr =>
      obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
      have hd := find_ok hfind
      have hDT := hP d (List.mem_of_find?_eq_some hd)
      have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
      obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
      obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInv hu hi
      have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
      have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
      have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      simp only [tstep, hterm, enter, hp, hd, hea, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subE ρ η ts.reverse, declCx d, rfl, ⟨hE.1, Coh_subE hE.2.1, CohR_subE hE.2.1 hE.2.2⟩, hbody, declCx_TvOK hDT hRI,
            ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun f rest h ws => by
              rw [hpw f rest h ws, ← use_ret hu]
              exact (hSub _ _ _ hsubr th.σs 0 0 ws).symm.trans (hPS _ _ Er ws)⟩
      · intro y en hen
        simp only [declCx, List.find?_cons, List.find?_nil] at hen
        split at hen
        · rename_i hy
          simp only [Option.some.injEq] at hen; subst hen
          have hy' : d.arg = y := by simpa using hy
          subst hy'
          refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
          rw [← shp_of_skel Ea, ← hs]
          exact (VR_call ts us η ρ d.argTy _ ws).1 (VR_sub hi1.1 hsub _ _ hv)
        · simp at hen
      · intro η' hx ws' hv' hl2
        obtain ⟨h2, hC⟩ := Ext_back (η₁ := subE ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
        have hv'' := (VR_coh (Coh_subE h2.1) hx.1 hx.2.1.symm hC _ _ _ _).2 hv'
        have hlr : Lay th.σs (substTs ts.reverse 0 0 (instT us 0 d.retTy)) (close (ts.map (close th.σs)).reverse d.retTy) ws' :=
          ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
        obtain ⟨hs2, hl3⟩ := Lay_canon hsubr hlr
        rw [← hC]
        refine hi1.2.2.1 _ h2 ws' ?_ hl3
        rw [← hs2]
        exact VR_sub hi1.1 hsubr _ _ ((VR_call ts us _ ρ d.retTy _ ws').2 hv'')
      · exact WitL_call hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
      · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.2.2.2.2.2.1 hi.2.2.2.2.1 hinst,
              WitAF_subE hi.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
              WitSh_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.1 hinst,
              WitC_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.1 hinst,
              WitN_call (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.2.2.2.1 hinst,
              WitR_call hi.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩

/-! ### Code values (2d-iv): `fnptr` and `callc` -/

theorem ev_agree {ρ ρA : Nat → Nat} {n : Nat} (hρ : ∀ k < n, ρ k = ρA k) :
    ∀ i : Idx, i.inScope n = true → ev ρ i = ev ρA i
  | .lit _, _ => rfl
  | .var k, h => by simp only [Idx.inScope, decide_eq_true_eq] at h; simp [ev, hρ k h]
  | .add i j, h => by
      simp only [Idx.inScope, Bool.and_eq_true] at h; simp [ev, ev_agree hρ i h.1, ev_agree hρ j h.2]
  | .sub i j, h => by
      simp only [Idx.inScope, Bool.and_eq_true] at h; simp [ev, ev_agree hρ i h.1, ev_agree hρ j h.2]
  | .smul m i, h => by simp only [Idx.inScope] at h; simp [ev, ev_agree hρ i h]

/-- Substitution does not move the skeleton of a type whose type variables are
all bound below `c`. -/
theorem substS_skel_wf (A : List Ty) : ∀ (v : Ty) (c ni : Nat), v.wf c ni = true →
    substS A c (skel v) = skel v := by
  intro v
  induction v with
  | tvar k => intro c ni h; simp only [Ty.wf, decide_eq_true_eq] at h; simp [skel, substS, h]
  | prod a b iha ihb =>
      intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, iha _ _ h.1, ihb _ _ h.2]
  | sum a b iha ihb =>
      intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, iha _ _ h.1, ihb _ _ h.2]
  | code a b iha ihb =>
      intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, iha _ _ h.1, ihb _ _ h.2]
  | array i t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | ptr μ t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | ptrOpt μ t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | loc μ t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | mu t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | tex κ t ih => intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS, ih _ _ h.2]
  | iall t ih => intro c ni h; simp only [Ty.wf] at h; simp only [skel, substS, ih _ _ h]
  | iex t ih => intro c ni h; simp only [Ty.wf] at h; simp only [skel, substS, ih _ _ h]
  | refine t ψ ih =>
      intro c ni h; simp only [Ty.wf, Bool.and_eq_true] at h; simp only [skel, substS_rf, ih _ _ h.2]
  | _ => intros; rfl

theorem skel_close_wf (σs : List Ty) {v : Ty} {ni : Nat} (h : v.wf 0 ni = true) :
    skel (close σs v) = skel v := by
  simp only [close, skel_substTs]; exact substS_skel_wf _ v 0 ni h

theorem findIdx_of_find {l : List Decl} {P : Decl → Bool} {d : Decl} (h : l.find? P = some d) :
    ∃ i, l.findIdx? P = some i ∧ l[i]? = some d := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
      by_cases hx : P x = true
      · simp only [List.find?_cons, hx, Option.some.injEq] at h
        subst h; exact ⟨0, by simp [List.findIdx?_cons, hx], rfl⟩
      · simp only [List.find?_cons, hx] at h
        obtain ⟨i, h1, h2⟩ := ih h
        exact ⟨i + 1, by simp [List.findIdx?_cons, hx, h1], by simpa using h2⟩

theorem Lay_code (σs : List Ty) {a b : Ty} {ni : Nat} (ha : a.wf 0 ni = true) (hb : b.wf 0 ni = true) (w : Word) :
    Lay σs (.code a b) (.code a b) [w] := by
  refine ⟨?_, ?_, by simp [wc, accs], by simp [Valid], ?_⟩
  · intro us hu; simp [accs] at hu; subst hu; simp [nWords, Acc.size]
  · rw [skel_close_wf σs (v := .code a b) (ni := ni) (by simp [Ty.wf, ha, hb])]
  · unfold close
    rw [substTs_TvB σs (.code a b) 0 0 (TvB_of_wf _ 0 ni (by simp [Ty.wf, ha, hb]))]

/-- Type equality moves no type variable: `guardT` agrees. -/
theorem guardT_tyEq {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) :
    ∀ k, t.guardT k = u.guardT k := by
  induction h with
  | refl => intro k; rfl
  | prod _ _ iha ihb | sum _ _ iha ihb | code _ _ iha ihb =>
      intro k; simp only [Ty.guardT, iha k, ihb k]
  | array _ _ ih | iall _ ih | iex _ ih | refine _ ih | refineIni _ _ ih =>
      intro k; simp only [Ty.guardT, ih k]
  | mu _ ih | tex _ ih => intro k; simp only [Ty.guardT, ih (k + 1)]
  | _ => intro k; rfl

/-- Subtyping keeps `guardT`, so a held value's type and the type it is
stored at are opaque-free alike. -/
theorem guardT_sub {cx : Cx} {t u : Ty} (h : SubS cx t u) : ∀ k, t.guardT k = true → u.guardT k = true := by
  induction h with
  | eq h => intro k hk; rw [← guardT_tyEq h k]; exact hk
  | intS => intro k _; rfl
  | refine _ ih => intro k hk; exact ih k hk
  | iniWeak h _ => intro k hk; simp only [Ty.guardT] at hk ⊢; rw [← guardT_tyEq h k]; exact hk
  | prod _ _ iha ihb | sum _ _ iha ihb =>
      intro k hk; simp only [Ty.guardT, Bool.and_eq_true] at hk ⊢; exact ⟨iha k hk.1, ihb k hk.2⟩
  | _ => intro k _; rfl

theorem sub_opaqueOK {cx c₁ : Cx} {t u : Ty} (h : SubS c₁ t u) (ho : cx.opaqueOK t = true) :
    cx.opaqueOK u = true := by
  unfold Cx.opaqueOK at ho ⊢
  rw [List.all_eq_true] at ho ⊢
  exact fun k hk => guardT_sub h k (ho k hk)

/-- **P1 + P4 at the thread, `fnptr`**: the block's position, `VR` at its own
signature (a well-formed closed signature is its own closure, `cl_wf`). -/
theorem tstep_fnptr {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x f : String} {e : Expr}
    (hp : g.p = p) (hP : ProgT p)
    (hterm : th.term = .let_ x (.fnptr f) e) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      have hk := OpT_retSk hop
      cases hop with
      | fnptr hfind htp hidx hb =>
          rename_i d
          have hd := find_ok hfind
          obtain ⟨i, hix, hpi⟩ := findIdx_of_find hd
          obtain ⟨hwa, hwr, -, -, -⟩ := hP d (List.mem_of_find?_eq_some hd)
          have hwa' : d.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
          have hwr' : d.retTy.wf 0 0 = true := by simpa [htp, hidx] using hwr
          have hn : d.name = f := by simpa using List.find?_some hd
          have hvr : VR ρ η (.code d.argTy d.retTy) (shp (.code d.argTy d.retTy)) [cst (.num i)] := by
            simp only [VR]
            refine ⟨i, d, rfl, by rw [hE.1]; exact hpi, by rw [hE.1, hn]; exact hd, htp, hidx,
              cl_wf _ hwa', cl_wf _ hwr'⟩
          simp only [tstep, hterm, evalOp, hp, hix, hd, List.map_cons, List.map_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInv hb hi hvr (Lay_code th.σs hwa' hwr' _), retPw_skel hPS hpw (skel_subst_eq hk th.σs 0 0 0)⟩

/-- **P1 + P4 at the thread, `callc`**: a call through a code value.  The
value's `VR` names the block, whose declared signature is the closure of the
static one; `VR_code` carries the argument in and the result out.  The callee runs in its
own view: no indices, no type variables (`CE η`). -/
theorem tstep_callc {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {f a : At} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.callc f a) e) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hSig : PwSig) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvE p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c'
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @callc c₁ _ _ _ _ tf σ τ t htf hc hu _ hsub hb =>
          obtain ⟨σ', τ', rfl⟩ : ∃ a b, tf = .code a b := by cases tf <;> simp_all [codeOf]
          simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨h1, h2⟩ := hc
          subst σ' τ'
          obtain ⟨rtf, wsf, hef, hvf, hlf⟩ := peek_VR hi.2.1 htf
          simp only [VR] at hvf
          obtain ⟨i, D, hwv, hpi, hfd, htp, hidx, lσ, lτ⟩ := hvf
          obtain ⟨w, rfl, hw⟩ := map_singleton hwv
          rw [hE.1] at hpi hfd
          have hDT := hP D (List.mem_of_find?_eq_some hfd)
          have hRI := ProgRetIall.ret D (List.mem_of_find?_eq_some hfd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          have hwa' : D.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
          have hwr' : D.retTy.wf 0 0 = true := by simpa [htp, hidx] using hwr
          -- the code value's runtime signature renders the static one; its
          -- `sig` is the block's (24e: pointees may differ)
          have hc : etok (skel rtf) = .code (etok (skel (close th.σs σ))) (etok (skel (close th.σs τ))) := hlf.2.1
          obtain ⟨ra, rr, rfl, hsa, hsr⟩ := eskel_eq_code hc
          -- (T3c-5a-4) both signature components are opaque-free (the argument
          -- is held, the result is bound), so their `sig` is their closure's,
          -- which is the block's (`VR`)
          have htbf := peek_tb htv htf
          simp only [tb, Bool.and_eq_true] at htbf
          have hoσ : cx.opaqueOK σ = true :=
            sub_opaqueOK hsub (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
          have hoτ : cx.opaqueOK τ = true := by
            have h := bind_opaqueOK hb; unfold Cx.opaqueOK at h ⊢; rwa [(use_opq hu).1] at h
          have hD : ∀ v : Ty, v.wf 0 0 = true → sig (clD v) = sig (close [] v) := fun v hv =>
            (sig_close_cl [] (fun _ => 0) (fun _ => .void) v 0 0 (fun k hk =>
              absurd (lt_of_guardT (tb_of_wf v hv) (Nat.le_refl 0) k (by simpa using hk))
                (Nat.not_lt_zero _))).symm
          have Ea : sig (close th.σs σ) = sig (close [] D.argTy) := by
            rw [sig_WitL hi.2.2.2.1 ρ hoσ (lt_of_guardT htbf.1 hi.2.2.2.2.1), lσ, hD _ hwa']
          have Er : sig rr = sig (close [] D.retTy) := by
            have e : sig rr = sig (close th.σs τ) := sig_of_eskel hsr
            rw [e, sig_WitL hi.2.2.2.1 ρ hoτ (lt_of_guardT htbf.2 hi.2.2.2.2.1), lτ, hD _ hwr']
          obtain ⟨hi1, rt0, ws, hea, hv, hl⟩ := use_FInv hu hi
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, hef, hw, hp, hpi, callFrame, enter, hfd, hea, retOf, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some, List.map_nil, List.reverse_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨fun _ => 0, CE η, declCx D, rfl, ⟨hE.1, Coh_CE η, CohR_CE η⟩, hbody, declCx_TvOK hDT hRI, ⟨Sat_nil _, ?_, ?_, ?_, ?_⟩,
            fun f rest h ws => by
              injection h with h1 h2; subst h1
              exact (hSig rr ws).symm.trans ((congrArg (fun t => TermPtrRts.pubWords t ws) Er).trans (hSig _ ws))⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : D.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move_sig hl' Ea⟩
              rw [← shp_of_sig Ea, ← hs]
              exact (VR_code hE.2.1 lσ _ _).1 (VR_sub hi1.1 hsub _ _ hv)
            · simp at hen
          · intro η' hx ws' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_back (η₁ := CE η) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hv'' : VR (fun _ => 0) (CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini)) D.retTy _ ws' :=
              (VR_coh hx.1 (Coh_CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini)) hx.2.1 hC.symm _ _ _ _).1 hv'
            have hw2 : wc (close [] D.retTy) = wc rr := (wc_of_sig Er).symm
            refine ⟨ρ, η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC, ⟨hE.1, h2.1, h2.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInv hb (FInv_ext hE.2.1 h2 hi1) ?_
              ⟨ShapeC_wc hw2 hl2.1, hsr, hw2 ▸ hl2.2.2.1, Valid_of_sig Er.symm hl2.2.2.2.1, by
                have hy := hlf.2.2.2.2
                simp only [close, substTs, lyt, etok, Ty.code.injEq] at hy
                exact hy.2⟩, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws⟩
            rw [shp_of_sig Er]; exact (VR_code h2.1 lτ _ _).2 hv''
          · exact ⟨fun k _ hk => by simp at hk, fun k σ h => by simp at h, fun k _ hk => by simp at hk⟩
          · exact ⟨by simp [declCx, htp], ⟨fun k hk => by simp [declCx, htp, KEnv.ask] at hk, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun _ h => by simp at h⟩, WitAF_CE η, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk⟩

/-! ### (P3 e) Calls and returns, resourceful

A call moves the argument's resources into the callee's frame and parks the
caller's remaining holdings on the stack; a return hands the result's
resources back and drops what the callee still holds (affine slack). -/

theorem VRR_instTs (us : List Idx) (η : TEnv) :
    ∀ (t : Ty) (d : Nat) (ρ : Nat → Nat) (rt : Shp) (ws : List Word) (R : Res),
      VRR ρ η (instT us d t) rt ws R ↔ VRR (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) η t rt ws R
  | .intS i, d, ρ, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .int, _, _, _, _, _ => by simp [instT, VRR]
  | .tid, _, _, _, _, _ => by simp [instT, VRR, VR]
  | .fix _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .lanes _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .refine t ψ, d, ρ, rt, ws, R => by
      simp only [instT, VRR]; exact and_congr (VRR_instTs us η t d ρ rt ws R) (by rw [TEnv.selIni_instT]; exact IniR_insts us d ρ _ ws ψ)
  | .iex b, d, ρ, rt, ws, R => by
      have e : ∀ v, vinsL (d + 1) (us.map (ev (fun k => vcons v ρ (k + (d + 1))))) (vcons v ρ) =
          vcons v (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vinsL_succ]
      simp only [instT, VRR]
      refine exists_congr fun n => exists_congr fun rb => exists_congr fun v =>
        and_congr_right fun _ => ?_
      rw [VRR_instTs us η b (d + 1) (vcons v ρ) rb ws R, e v]
  | .prod a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, VRR_instTs us η a d ρ, VRR_instTs us η b d ρ]
  | .unit, _, _, _, _, _ => by simp [instT, VRR]
  | .void, _, _, _, _, _ => by simp [instT, VRR]
  | .sum a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, VRR_instTs us η a d ρ, VRR_instTs us η b d ρ, VRR_instTs us η.unsee a d ρ,
        VRR_instTs us η.unsee b d ρ]
  | .code a b, d, ρ, rt, ws, R => by
      simp only [instT, VRR, cl_instTs]
  | .array _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .ptr _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_instTs, ModeOK_inst, ownW_inst]
  | .ptrOpt _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_instTs, ModeOK_inst, ownW_inst]
  | .loc _ _, _, _, _, _, _ => by simp only [instT, VRR, cl_instTs, ModeOK_inst, modeIni_inst, ownW_inst]
  | .share _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .cap _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .word _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .tok _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .word2 _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .tok2 _ _ _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .epair _ _, _, _, _, _, _ => by simp [instT, VRR]
  | .tokE _ _ _, _, _, _, _, _ => by simp [instT, VRR, ev_instIs]
  | .tvar _, _, _, _, _, _ => by simp [instT, VRR]
  | .mu b, d, ρ, rt, ws, R => by
      have e := cl_instTs us d ρ η.wit (.mu b)
      simp only [instT] at e
      simp only [instT, VRR, e]
      exact VRR_instTs us _ b d ρ rt ws R
  | .iall b, d, ρ, rt, ws, R => by
      have e : ∀ v, vinsL (d + 1) (us.map (ev (fun k => vcons v ρ (k + (d + 1))))) (vcons v ρ) =
          vcons v (vinsL d (us.map (ev (fun k => ρ (k + d)))) ρ) := by
        intro v
        have hf : (fun k => vcons v ρ (k + (d + 1))) = fun k => ρ (k + d) := by
          funext k; exact vcons_succ v ρ (k + d)
        rw [hf, vinsL_succ]
      simp only [instT, VRR]
      refine forall_congr' fun v => ?_
      rw [VRR_instTs us η b (d + 1) (vcons v ρ) rt ws R, e v]
  | .tex κ b, d, ρ, rt, ws, R => by
      simp only [instT, VRR]
      exact exists_congr fun n => exists_congr fun rb => exists_congr fun s => and_congr_right fun _ =>
        and_congr_right fun _ => and_congr_right fun _ => VRR_instTs us (η.push0 s) b d ρ rb ws R

/-- Row 18 with resources. -/
theorem VRR_call (ts : List Ty) (us : List Idx) (η : TEnv) (ρ : Nat → Nat) (u : Ty) (rt : Shp)
    (ws : List Word) (R : Res) :
    VRR ρ η (substTs ts.reverse 0 0 (instT us 0 u)) rt ws R ↔
      VRR (vinsL 0 (us.map (ev ρ)) ρ) (subE ρ η ts.reverse) u rt ws R := by
  rw [show VRR ρ η (substTs ts.reverse 0 0 (instT us 0 u)) rt ws R ↔ _ from
    VRR_substTs ts.reverse η ρ _ [] 0 ρ rt ws R (fun k => rfl), VRR_instTs]
  rfl

/-- The callee's entry frame holds exactly its argument's resources. -/
theorem declCx_HeldOK {ρ : Nat → Nat} {η : TEnv} {d : Decl} {rt : Ty} {ws : List Word} {R : Res}
    (hv : VRR ρ η d.argTy (shp rt) ws R) : HeldOK ρ η (declCx d) [(d.arg, rt, ws)] R := by
  refine ⟨by simp [declCx], by simp [declCx], by simp [declCx], fun _ => R, ?_, ?_⟩
  · intro y e hf _
    simp only [declCx, List.find?_cons, List.find?_nil] at hf
    split at hf
    · rename_i hy
      simp only [Option.some.injEq] at hf; subst hf
      have hy' : d.arg = y := by simpa using hy
      subst hy'
      exact ⟨rt, ws, by simp [lookupE], hv⟩
    · simp at hf
  · simp [declCx, Holds]
    exact Res.le_refl _


theorem Res_le_of_add_le {R Rr Rf : Res} (h : R + Rr ≤ Rf) : R ≤ Rf := fun k => by
  have := h k; simp only [Res.add_apply] at this; omega

/-- **P3 at the thread, `ret`** into a caller frame: the returned value's `R`
joins the caller's `Rc`; the callee's leftover is dropped. -/
theorem tstep_retR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {Rf Rs : Res}
    (hterm : th.term = .ret a) (hst : th.stack ≠ []) (hT : Typed p cx th.term)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT
  cases hT with
  | ret hu _ hsub =>
      obtain ⟨rt, ws, R, Rr, hea, hv, hl, hvr, hi1, hle⟩ := useR hu hi hE.2.2
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      have hK := hi1.2.1 η (Ext_refl hE.2.1 hE.2.2) ws R
        (by rw [← hs]; exact VRR_sub hi1.1.1 hsub _ _ _ hvr) hl'
      cases hstk : th.stack with
      | nil => exact absurd hstk hst
      | cons f rest =>
          rw [hstk] at hK
          obtain ⟨Rc, Rrest, hRs, ρ', η', c, hCE, -, hE', hc, hvc, hf, hpwF⟩ := hK
          simp only [tstep, hterm, hstk, hea]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨ρ', η', c, Rc + Rf, Rrest, hCE, hE', hc, hvc,
            FInvR_mono hf (Res.add_le_add (Res.le_refl _) (Res_le_of_add_le hle)), ?_, hpwF⟩
          rw [hRs]
          exact Res.ext fun k => by simp only [Res.add_apply]; omega

/-- Splitting a frame's bound: `Rf - Rr` and `Rr`. -/
theorem Res_split {R Rr Rf : Res} (h : R + Rr ≤ Rf) :
    ∃ Rf' : Res, R ≤ Rf' ∧ ∀ Rs : Res, Rf' + (Rr + Rs) = Rf + Rs := by
  refine ⟨fun k => Rf k - Rr k, fun k => ?_, fun Rs => Res.ext fun k => ?_⟩
  · have := h k; simp only [Res.add_apply] at this; show R k ≤ Rf k - Rr k; omega
  · have := h k; simp only [Res.add_apply] at this ⊢; show Rf k - Rr k + (Rr k + Rs k) = Rf k + Rs k; omega

/-- **P3 at the thread, `call`.**  The argument's `R` moves to the callee's
frame (bound `Rf - Rr`); the caller's leftover `Rr` waits in the pushed frame. -/
theorem tstep_callR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    {Rf Rs : Res}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.call f is a ts) e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) [hPW : TermA4.ProgCkWC p]
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPw th.σs th.stack cx.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c'
      obtain ⟨c', -, hop, he, hck, hoa⟩ := TermA4.CkW_let hCk
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @call _ _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hb =>
          obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
          have hd := find_ok hfind
          have hDT := hP d (List.mem_of_find?_eq_some hd)
          have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          obtain ⟨rt0, ws, R, Rr, hea, hv, hl, hvr, hi1, hle⟩ := useR hu hi hE.2.2
          obtain ⟨Rf', hR', hsum⟩ := Res_split hle
          have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
          have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
          have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, callFrame, enter, hp, hd, hea, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subE ρ η ts.reverse, declCx d, Rf', Rr + Rs, rfl,
            ⟨hE.1, Coh_subE hE.2.1, CohR_subE hE.2.1 hE.2.2⟩, ⟨hbody, TermA4.CkW_call (ρ₀ := ρ) hCk.2.2 (fun k => (hE.2.1 k).1.1) hinst (TermA4.opArgOK_call hoa)
              (hPW.ck d (List.mem_of_find?_eq_some hd))⟩, declCx_TvOK hDT hRI,
            ⟨⟨Sat_nil _, ?_, fun _ _ _ _ _ => trivial, ?_, ?_⟩, ?_, HeldOK_mono (declCx_HeldOK ?_) hR'⟩, hsum Rs,
            fun f rest h ws => by injection h with h1 h2; subst h1; rfl⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : d.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
              rw [← shp_of_skel Ea, ← hs]
              exact (VR_call ts us η ρ d.argTy _ ws).1 (VR_sub hi1.1.1 hsub _ _ hv)
            · simp at hen
          · exact WitL_call hi.1.2.2.2.1 hi.1.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
          · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.1.2.2.2.2.2.1 hi.1.2.2.2.2.1 hinst,
              WitAF_subE hi.1.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
              WitSh_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.1 hinst,
              WitC_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.2.1 hinst,
              WitN_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.2.2.1 hinst,
              WitR_call hi.1.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩
          · intro η' hx ws' R' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_back (η₁ := subE ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hr2 := h2.2.2.2.2.2.2.2.2.2.2.1
            have hv'' := (VRR_coh (Coh_subE h2.1) (CohR_subE h2.1 hr2) hx.1 hx.2.2.2.2.2.2.2.2.2.2.1
              hx.2.1.symm hC _ _ _ _ _).2 hv'
            have hrid : (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini).rid = η'.rid :=
              Nat.max_eq_right hx.2.2.2.2.2.2.2.2.2.1
            refine ⟨Rr, Rs, rfl, ρ, η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC,
              hrid, ⟨hE.1, h2.1, hr2⟩, ⟨he, hck⟩, htv',
              bindR hb (FInvR_ext hE.2.1 hE.2.2 h2 hi1) (RLink_of h2.1 hr2)
                ((VRR_call ts us _ ρ d.retTy _ ws' R').2 hv'') ?_, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws⟩
            exact ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
          · rw [← shp_of_skel Ea, ← hs]
            exact (VRR_call ts us η ρ d.argTy _ ws R).1 (VRR_sub hi1.1.1 hsub _ _ _ hvr)

/-- **P3 at the thread, `tail`.**  No frame is pushed: the callee holds the
argument (within `Rf`) and returns into the current continuation. -/
theorem tstep_tailR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {f : String} {is : List String} {a : At} {ts : List Ty}
    {Rf Rs : Res}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .tail f is a ts) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) [hPW : TermA4.ProgCkWC p]
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hZ : ZeroCloseP)
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hpw : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | @tail _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub hsubr =>
      obtain ⟨us, hlen, rfl, rfl⟩ := instantiate_ok hinst
      have hd := find_ok hfind
      have hDT := hP d (List.mem_of_find?_eq_some hd)
      have hRI := ProgRetIall.ret d (List.mem_of_find?_eq_some hd)
      obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
      obtain ⟨rt0, ws, R, Rr, hea, hv, hl, hvr, hi1, hle⟩ := useR hu hi hE.2.2
      have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
      have Er := skel_call th.σs ts us d.retTy (hlen ▸ TvB_skel _ _ _ hwr)
      have Lr := lyt_call th.σs ts us d.retTy (hlen ▸ TvB_of_wf _ _ _ hwr)
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      simp only [tstep, hterm, enter, hp, hd, hea, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨vinsL 0 (us.map (ev ρ)) ρ, subE ρ η ts.reverse, declCx d, Rf, Rs, rfl,
        ⟨hE.1, Coh_subE hE.2.1, CohR_subE hE.2.1 hE.2.2⟩, ⟨hbody, TermA4.CkW_call (ρ₀ := ρ) hCk.2.2 (fun k => (hE.2.1 k).1.1) hinst (TermA4.checkW_tail_args hCk.1)
          (hPW.ck d (List.mem_of_find?_eq_some hd))⟩, declCx_TvOK hDT hRI,
        ⟨⟨Sat_nil _, ?_, fun _ _ _ _ _ => trivial, ?_, ?_⟩, ?_,
          HeldOK_mono (declCx_HeldOK ?_) (Res_le_of_add_le hle)⟩, rfl,
        fun f rest h ws => by
          rw [hpw f rest h ws, ← use_ret hu]
          exact (hSub _ _ _ hsubr th.σs 0 0 ws).symm.trans (hPS _ _ Er ws)⟩
      · intro y en hen
        simp only [declCx, List.find?_cons, List.find?_nil] at hen
        split at hen
        · rename_i hy
          simp only [Option.some.injEq] at hen; subst hen
          have hy' : d.arg = y := by simpa using hy
          subst hy'
          refine ⟨_, ws, by simp [lookupE], ?_, Lay_move hl' Ea⟩
          rw [← shp_of_skel Ea, ← hs]
          exact (VR_call ts us η ρ d.argTy _ ws).1 (VR_sub hi1.1.1 hsub _ _ hv)
        · simp at hen
      · exact WitL_call hi.1.2.2.2.1 hi.1.2.2.2.2.1 (fun k => (hE.2.1 k).1) (instantiate_ts hinst)
      · exact ⟨by simp [declCx, hlen], KindsOK_call hZ hi.1.2.2.2.2.2.1 hi.1.2.2.2.2.1 hinst,
          WitAF_subE hi.1.2.2.2.2.2.2.1 (instantiate_arrFree hinst)
                (fun σ h => (hrt σ (List.mem_reverse.1 h)).2) (fun k => (hE.2.1 k).1)
                (fun σ h => mg_of_wf σ (instantiate_ts hinst σ (List.mem_reverse.1 h)).2),
          WitSh_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.1 hinst,
          WitC_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.2.1 hinst,
          WitN_call (fun k => (hE.2.1 k).1) hi.1.2.2.2.2.2.2.2.2.2.1 hinst,
          WitR_call hi.1.2.2.2.2.2.2.2.2.2.2 hinst (fun σ h => (hrt σ h).1)⟩
      · intro η' hx ws' R' hv' hl2
        obtain ⟨h2, hC⟩ := Ext_back (η₁ := subE ρ η ts.reverse) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
        have hr2 := h2.2.2.2.2.2.2.2.2.2.2.1
        have hv'' := (VRR_coh (Coh_subE h2.1) (CohR_subE h2.1 hr2) hx.1 hx.2.2.2.2.2.2.2.2.2.2.1
          hx.2.1.symm hC _ _ _ _ _).2 hv'
        have hrid : (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini).rid = η'.rid :=
          Nat.max_eq_right hx.2.2.2.2.2.2.2.2.2.1
        have hlr : Lay th.σs (substTs ts.reverse 0 0 (instT us 0 d.retTy)) (close (ts.map (close th.σs)).reverse d.retTy) ws' :=
          ⟨hl2.1, (eskel_of_skel Er).symm, hl2.2.2.1, hl2.2.2.2.1, (elyt_of_lyt Lr).symm⟩
        obtain ⟨hs2, hl3⟩ := Lay_canon hsubr hlr
        have hK := hi1.2.1 _ h2 ws' R' (by
          rw [← hs2]
          exact VRR_sub hi1.1.1 hsubr _ _ _ ((VRR_call ts us _ ρ d.retTy _ ws' R').2 hv'')) hl3
        rw [hC, hrid] at hK
        exact hK
      · rw [← shp_of_skel Ea, ← hs]
        exact (VRR_call ts us η ρ d.argTy _ ws R).1 (VRR_sub hi1.1.1 hsub _ _ _ hvr)

/-- A closure call's callee view: the thread-wide part, keeping the caller's
region counter (`CE` resets it). -/
def CER (η : TEnv) : TEnv := { CE η with rid := η.rid }

theorem CE_CER (η : TEnv) : CE (CER η) = CE η := rfl

theorem Coh_CER (η : TEnv) : Coh (CER η) := Coh_CE η

theorem CohR_CER (η : TEnv) : CohR (CER η) := CohR_CE η

theorem VR_CER {η : TEnv} (ρ : Nat → Nat) (t : Ty) (S : Shp) (ws : List Word) :
    VR ρ (CE η) t S ws ↔ VR ρ (CER η) t S ws :=
  VR_coh (Coh_CE η) (Coh_CER η) rfl rfl ρ t S ws

theorem VRR_CER {η : TEnv} (ρ : Nat → Nat) (t : Ty) (S : Shp) (ws : List Word) (X : Res) :
    VRR ρ (CE η) t S ws X ↔ VRR ρ (CER η) t S ws X :=
  VRR_coh (Coh_CE η) (CohR_CE η) (Coh_CER η) (CohR_CER η) rfl rfl ρ t S ws X

/-- **P3 at the thread, `callc`**: a call through a code value; the callee
runs in its own view (`CE η`, no indices), holding the argument's `R`. -/
theorem tstep_callcR {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {f a : At} {e : Expr} {Rf Rs : Res}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.callc f a) e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) [hPW : TermA4.ProgCkWC p]
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hpw : RetPw th.σs th.stack cx.ret) (hSig : PwSig) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
      rename_i c'
      obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
      have htv' := OpT_TvOK hP hop htv
      cases hop with
      | @callc c₁ _ _ _ _ tf σ τ t htf hc hu _ hsub hb =>
          obtain ⟨σ', τ', rfl⟩ : ∃ a b, tf = .code a b := by cases tf <;> simp_all [codeOf]
          simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨h1, h2⟩ := hc
          subst σ' τ'
          obtain ⟨rtf, wsf, hef, hvf, hlf⟩ := peek_VR hi.1.2.1 htf
          simp only [VR] at hvf
          obtain ⟨i, D, hwv, hpi, hfd, htp, hidx, lσ, lτ⟩ := hvf
          obtain ⟨w, rfl, hw⟩ := map_singleton hwv
          rw [hE.1] at hpi hfd
          have hDT := hP D (List.mem_of_find?_eq_some hfd)
          have hRI := ProgRetIall.ret D (List.mem_of_find?_eq_some hfd)
          obtain ⟨hwa, hwr, -, -, hbody⟩ := id hDT
          have hwa' : D.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
          have hwr' : D.retTy.wf 0 0 = true := by simpa [htp, hidx] using hwr
          have hc : etok (skel rtf) = .code (etok (skel (close th.σs σ))) (etok (skel (close th.σs τ))) := hlf.2.1
          obtain ⟨ra, rr, rfl, hsa, hsr⟩ := eskel_eq_code hc
          have htbf := peek_tb htv htf
          simp only [tb, Bool.and_eq_true] at htbf
          have hoσ : cx.opaqueOK σ = true :=
            sub_opaqueOK hsub (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
          have hoτ : cx.opaqueOK τ = true := by
            have h := bind_opaqueOK hb; unfold Cx.opaqueOK at h ⊢; rwa [(use_opq hu).1] at h
          have hD : ∀ v : Ty, v.wf 0 0 = true → sig (clD v) = sig (close [] v) := fun v hv =>
            (sig_close_cl [] (fun _ => 0) (fun _ => .void) v 0 0 (fun k hk =>
              absurd (lt_of_guardT (tb_of_wf v hv) (Nat.le_refl 0) k (by simpa using hk))
                (Nat.not_lt_zero _))).symm
          have Ea : sig (close th.σs σ) = sig (close [] D.argTy) := by
            rw [sig_WitL hi.1.2.2.2.1 ρ hoσ (lt_of_guardT htbf.1 hi.1.2.2.2.2.1), lσ, hD _ hwa']
          have Er : sig rr = sig (close [] D.retTy) := by
            have e : sig rr = sig (close th.σs τ) := sig_of_eskel hsr
            rw [e, sig_WitL hi.1.2.2.2.1 ρ hoτ (lt_of_guardT htbf.2 hi.1.2.2.2.2.1), lτ, hD _ hwr']
          obtain ⟨rt0, ws, R, Rr, hea, hv, hl, hvr, hi1, hle⟩ := useR hu hi hE.2.2
          obtain ⟨Rf', hR', hsum⟩ := Res_split hle
          obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
          simp only [tstep, hterm, hef, hw, hp, hpi, callFrame, enter, hfd, hea, retOf, Option.bind, bind, pure,
            Option.map_some, ol, Option.toList_some, List.map_nil, List.reverse_nil]
          refine ⟨by simp, ?_⟩
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨fun _ => 0, CER η, declCx D, Rf', Rr + Rs, rfl, ⟨hE.1, Coh_CER η, CohR_CER η⟩, ⟨hbody, TermA4.CkW_decl (hPW.ck D (List.mem_of_find?_eq_some hfd)) (TermA4.WitA_void (fun _ => rfl))⟩,
            declCx_TvOK hDT hRI,
            ⟨⟨Sat_nil _, ?_, fun _ _ _ _ _ => trivial, ?_, ?_⟩, ?_, HeldOK_mono (declCx_HeldOK ?_) hR'⟩, hsum Rs,
            fun f rest h ws => by
              injection h with h1 h2; subst h1
              exact (hSig rr ws).symm.trans ((congrArg (fun t => TermPtrRts.pubWords t ws) Er).trans (hSig _ ws))⟩
          · intro y en hen
            simp only [declCx, List.find?_cons, List.find?_nil] at hen
            split at hen
            · rename_i hy
              simp only [Option.some.injEq] at hen; subst hen
              have hy' : D.arg = y := by simpa using hy
              subst hy'
              refine ⟨_, ws, by simp [lookupE], ?_, Lay_move_sig hl' Ea⟩
              rw [← shp_of_sig Ea, ← hs]
              exact (VR_CER _ _ _ _).1 ((VR_code hE.2.1 lσ _ _).1 (VR_sub hi1.1.1 hsub _ _ hv))
            · simp at hen
          · exact ⟨fun k _ hk => by simp at hk, fun k σ h => by simp at h, fun k _ hk => by simp at hk⟩
          · exact ⟨by simp [declCx, htp], ⟨fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun _ h => by simp at h⟩, WitAF_CE η, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk, fun k hk => by simp [declCx, htp, KEnv.ask] at hk,
              fun k hk => by simp [declCx, htp, KEnv.ask] at hk⟩
          · intro η' hx ws' R' hv' hl2
            obtain ⟨h2, hC⟩ := Ext_back (η₁ := CER η) hE.2.1 hx rfl rfl rfl rfl rfl rfl rfl rfl
            have hr2 := h2.2.2.2.2.2.2.2.2.2.2.1
            have hv'' : VRR (fun _ => 0) (CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini))
                D.retTy _ ws' R' :=
              (VRR_coh hx.1 hx.2.2.2.2.2.2.2.2.2.2.1
                (Coh_CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini))
                (CohR_CE (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini))
                hx.2.1 hC.symm _ _ _ _ _).1 hv'
            have hrid : (η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini).rid = η'.rid :=
              Nat.max_eq_right hx.2.2.2.2.2.2.2.2.2.1
            have hw2 : wc (close [] D.retTy) = wc rr := (wc_of_sig Er).symm
            refine ⟨Rr, Rs, rfl, ρ, η.withSto η'.sto η'.ini η'.pfr η'.seen η'.box (max η.rid η'.rid) η'.fp η'.rini, c', hC,
              hrid, ⟨hE.1, h2.1, hr2⟩, ⟨he, hck⟩, htv',
              bindR hb (FInvR_ext hE.2.1 hE.2.2 h2 hi1) (RLink_of h2.1 hr2) ?_
              ⟨ShapeC_wc hw2 hl2.1, hsr, hw2 ▸ hl2.2.2.1, Valid_of_sig Er.symm hl2.2.2.2.1, by
                have hy := hlf.2.2.2.2
                simp only [close, substTs, lyt, etok, Ty.code.injEq] at hy
                exact hy.2⟩, fun f rest h ws => by rw [bind_ret hb, use_ret hu]; exact hpw f rest h ws⟩
            rw [shp_of_sig Er]; exact (VRR_code h2.1 hr2 lτ _ _ _).2 hv''
          · rw [← shp_of_sig Ea, ← hs]
            exact (VRR_CER _ _ _ _ _).1 ((VRR_code hE.2.1 hE.2.2 lσ _ _ _).1 (VRR_sub hi1.1.1 hsub _ _ _ hvr))

#print axioms VRR_call
#print axioms declCx_HeldOK
#print axioms tstep_retR
#print axioms tstep_callR
#print axioms tstep_tailR
#print axioms tstep_callcR


#print axioms tstep_pure
#print axioms sig_close_cl
#print axioms sig_WitL
#print axioms VR_ext
#print axioms VR_coh
#print axioms FInv_ext
#print axioms Coh_withSto
#print axioms WitL_call
#print axioms accs_cl_close
#print axioms accs_WitL
#print axioms countI_cl_eq
#print axioms countT_cl_eq
#print axioms accs_shiftT
#print axioms zrel_WitL
#print axioms pushT_FInv
#print axioms KindsOK_call
#print axioms accs_close
#print axioms wordFree_close
#print axioms tstep_ifeq
#print axioms tstep_parity
#print axioms tstep_split
#print axioms tstep_unpack
#print axioms tstep_ifnull
#print axioms VR_up
#print axioms VR_sub
#print axioms accs_width
#print axioms shp_wc
#print axioms VR_agree
#print axioms accs_shiftI
#print axioms shp_shiftI
#print axioms skel_substTs
#print axioms wc_iex
#print axioms info_sub
#print axioms shp_sub
#print axioms tstep_inl
#print axioms tstep_inr
#print axioms tstep_case
#print axioms Valid_sub
#print axioms Valid_skel
#print axioms decodeArm_mono
#print axioms roundtrip
#print axioms asArm_valid
#print axioms tstep_call
#print axioms tstep_tail
#print axioms tstep_ret
#print axioms VR_call
#print axioms skel_call
#print axioms substS_comp
#print axioms tstep_fnptr
#print axioms tstep_callc
#print axioms VR_close
#print axioms VR_code
#print axioms Coh_subE
#print axioms Coh_consC
#print axioms VR_substTs
#print axioms cl_subE
#print axioms tstep_unpackT
#print axioms unpackT_step
#print axioms pure_pres
#print axioms pure_progress
#print axioms pushT_FInv
#print axioms VR_relsG
#print axioms VR_mono
#print axioms sig_pack
#print axioms VR_shiftT
#print axioms VR_unfold
#print axioms WitAF_subE
#print axioms noIallV_cl
#print axioms WitAF.af
#print axioms WitAF.ni
#print axioms unguarded_of_guardT

/-! ### T3c-5d: re-boxing, and moving values between the thread's and memory's view -/

/-- (T3c-5d) The head sum of a shape, if any, is boxed (through `iex`/`tex`);
a pair shape is excluded. -/
def bh : Shp → Prop
  | .sum _ R => R.tier = .boxed
  | .iex _ b => bh b
  | .tex _ b => bh b
  | .prod _ _ => False
  | _ => True

theorem bh_shp : ∀ t : Ty, isBoxed t = true → bh (shp t)
  | .sum a b, h => by
      simp only [isBoxed, sumHead, Bool.true_and, beq_iff_eq] at h
      simp only [shp, bh, tier_lnorm, h]
  | .refine t ψ, h => by
      simp only [isBoxed, sumHead, tier_refine] at h
      exact bh_shp t (by simpa [isBoxed] using h)
  | .mu t, h => by
      simp only [isBoxed, sumHead, tier_mu] at h
      exact bh_shp t (by simpa [isBoxed] using h)
  | .iex t, h => by
      simp only [isBoxed, sumHead, tier_iex] at h
      exact bh_shp t (by simpa [isBoxed] using h)
  | .tex κ t, h => by
      simp only [isBoxed, sumHead, tier_tex] at h
      exact bh_shp t (by simpa [isBoxed] using h)
  | .iall t, h => by
      simp only [isBoxed, sumHead, tier_iall] at h
      exact bh_shp t (by simpa [isBoxed] using h)
  | .intS _, h | .int, h | .fix _ _, h | .lanes _ _, h | .prod _ _, h | .code _ _, h | .tvar _, h
  | .ptr _ _, h | .ptrOpt _ _, h | .loc _ _, h | .unit, h | .void, h | .array _ _, h | .share _, h
  | .cap _ _, h | .word _ _, h | .tok _ _, h | .word2 _ _, h | .tok2 _ _ _ _, h | .epair _ _, h | .tokE _ _ _, h => by simp [isBoxed, sumHead] at h

theorem IniR_ren {ρ : Nat → Nat} {ini : WeakMem.AllocLabel → Nat} {w1 w2 : Word} {x1 x2 : WeakMem.Address}
    (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (hi : ini x1.label ≤ ini x2.label) :
    ∀ ψ : Pred, IniR ρ ini ψ [w1] → IniR ρ ini ψ [w2]
  | .ini k, h => by
      simp only [IniR, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1, h2] at h ⊢
      intro a ha; cases ha; exact Nat.le_trans (h x1 rfl) hi
  | .and p q, h => ⟨IniR_ren h1 h2 hi p h.1, IniR_ren h1 h2 hi q h.2⟩
  | .le _ _, _ | .eq _ _, _ | .tt, _ => by simp [IniR]



/-- (T3c-5d) **Re-boxing**: in a view with no type-variable relations, a
reference to box `x1` read at tag offset `s1` is valid wherever a reference to
box `x2` holding the same arm (`tag − s`) and a newer payload, read at `s2`, is. -/
theorem VR_ren0 (w1 w2 : Word) (x1 x2 : WeakMem.Address) (B1 B2 : Box)
    (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (ho2 : x2.offset = 0)
    (hpay : WLe B1.pay B2.pay) :
    ∀ (t : Ty) (η : TEnv) (ρ : Nat → Nat) (R : Shp) (s1 s2 : Nat),
      B1.tag + s2 = B2.tag + s1 →
      (∀ k S ws, ¬ η.rels k S ws) → bh R →
      η.box x1.label = some B1 → η.box x2.label = some B2 → η.sto x1.label = none →
      η.ini x1.label ≤ η.ini x2.label → min (η.ini x1.label) (η.rini x1.label) ≤ η.rini x2.label → (BoxSeen η x2.label B2 ∨ B2.fr ≤ w2.view) →
      VR ρ η t (vsh s1 R) [w1] → VR ρ η t (vsh s2 R) [w2] := by
  intro t
  induction t with
  | unit | array | share | cap | tok | tok2 | tokE => intros; simp [VR]
  -- two words cannot be one
  | word2 | epair =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp [VR] at h
  | word r P =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VR] at h ⊢
      refine ⟨h.1, fun hg => ?_⟩
      obtain ⟨n, hn, _⟩ := h.2 hg
      simp [h1] at hn
  | iall b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      exact fun n => ih η (vcons n ρ) R s1 s2 ht hr hR hb1 hb2 hs hi hri hm (h n)
  | void => intros; simp_all [VR]
  | int => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VR, h1] at h
  | tid =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VR] at h
      obtain ⟨l, c, he, hc, -⟩ := h
      simp only [List.map_cons, List.map_nil, h1, List.cons.injEq] at he
      have hl : x1.label = l := by cases he.1; rfl
      rw [hl, hc] at hs; cases hs
  | intS => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VR, h1] at h
  | code => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VR, h1] at h
  | tvar k => intro η ρ R s1 s2 _ hr _ _ _ _ _ _ _ h; simp only [VR, TEnv.get] at h; obtain ⟨_, _, h⟩ := h; exact absurd h (hr _ _ _)
  | ptr _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VR, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      obtain ⟨a, c, ha, _, hc, _⟩ := h; cases ha; rw [hs] at hc; cases hc
  | ptrOpt _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VR, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      rcases h with h | ⟨a, c, ha, _, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | loc _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VR, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      rcases h with ⟨h, _⟩ | ⟨a, c, _, ha, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | fix _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VR] at h; obtain ⟨_, n, hn, _⟩ := h; simp [h1] at hn
  | lanes _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VR] at h; obtain ⟨_, n, hn⟩ := h; simp [h1] at hn
  | refine t ψ ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      exact ⟨ih η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h.1, IniR_ren h1 h2 (TEnv.selIni_le_at η t hi hri) ψ h.2⟩
  | mu b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      refine ih _ ρ R s1 s2 ht ?_ hR hb1 hb2 hs hi hri hm h
      intro k S ws hk
      cases k with
      | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
      | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)
  | prod a b _ _ =>
      intro η ρ R s1 s2 _ _ hR _ _ _ _ _ _ h
      simp only [VR] at h
      obtain ⟨ra, rb, hr, _⟩ := h
      cases R <;> simp_all [vsh, bh]
  | iex b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      obtain ⟨n, rb, w, hrt, hv⟩ := h
      cases R with
      | iex m r0 =>
          simp only [vsh, Shp.iex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          exact ⟨m, vsh s2 r0, w, rfl, ih η _ r0 s1 s2 ht hr hR hb1 hb2 hs hi hri hm hv⟩
      | _ => simp [vsh] at hrt
  | tex κ b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      obtain ⟨n, rb, s, hrt, hc, hk, hv⟩ := h
      cases R with
      | tex m r0 =>
          simp only [vsh, Shp.tex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          refine ⟨m, vsh s2 r0, s, rfl, hc, hk, ih _ ρ r0 s1 s2 ht ?_ hR hb1 hb2 hs hi hri hm hv⟩
          intro k S ws hk
          cases k with
          | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
          | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)
      | _ => simp [vsh] at hrt
  | sum a b iha ihb =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VR] at h ⊢
      obtain ⟨n, Ra, Rb, hrt, h⟩ := h
      cases R with
      | sum m R0 =>
          simp only [vsh, Shp.sum.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          simp only [bh] at hR
          rcases h with ⟨htr, x, s, B, hw, ho, hb, hn, ⟨hsB, hwa⟩, hmo, hA, hB⟩ | ⟨j, p, hd, _, _⟩
          · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at hw
            cases hw
            rw [hb1] at hb; cases hb
            have hn' : s = s1 := by simp at hn; omega
            subst s
            have hpl : B1.pay.length = B2.pay.length := by simpa using congrArg List.length hpay.vals
            refine ⟨_, Ra, Rb, rfl, Or.inl ⟨htr, x2, s2, B2, by simp [h2], ho2, hb2, rfl,
              ⟨by omega, by rw [show B2.tag - s2 = B1.tag - s1 by omega, ← hpl]; exact hwa⟩,
              by rcases hm with hm | hm; exact Or.inl hm; exact Or.inr (by simpa using hm), fun hj => ?_, fun hj => ?_⟩⟩
            · have e : B2.tag - s2 = B1.tag - s1 := by omega
              rw [e] at hj ⊢
              refine ⟨fun hx => iha η ρ (shp Ra) s1 s2 ht hr (bh_shp Ra hx) hb1 hb2 hs hi hri hm ((hA hj).1 hx),
                fun hx => ?_⟩
              obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 hx
              obtain ⟨q', hq', hw'⟩ := ofArm_wle hpay hq
              exact ⟨q', hq', ShapeC_vals hw'.vals hs1, hw1, Valid_vals _ _ _ hw'.vals hv1, VR_up _ _ _ _ hw' hv⟩
            · have e : B2.tag - s2 = B1.tag - s1 := by omega
              rw [e] at hj ⊢
              refine ⟨fun hx => ihb η ρ (shp Rb) (s1 + (armsOf Ra).length) (s2 + (armsOf Ra).length) (by omega)
                hr (bh_shp Rb hx) hb1 hb2 hs hi hri hm ((hB hj).1 hx), fun hx => ?_⟩
              obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hB hj).2 hx
              obtain ⟨q', hq', hw'⟩ := ofArm_wle hpay hq
              exact ⟨q', hq', ShapeC_vals hw'.vals hs1, hw1, Valid_vals _ _ _ hw'.vals hv1, VR_up _ _ _ _ hw' hv⟩
          · rw [hR] at hd; simp [decodeArm] at hd
      | _ => simp [vsh] at hrt



/-- (T3c-5d) A real boxed value's shape carries tag offset 0. -/
theorem vsh_zero : ∀ t : Ty, isBoxed t = true → vsh 0 (shp t) = shp t
  | .sum a b, h => by
      simp only [isBoxed, sumHead, Bool.true_and, beq_iff_eq] at h
      have e : wc (.sum a b) = some 1 := by simp [wc, accs, h, nWords, Acc.size]
      simp only [shp, vsh, e]
  | .refine t ψ, h => by
      simp only [isBoxed, sumHead, tier_refine] at h
      exact vsh_zero t (by simpa [isBoxed] using h)
  | .mu t, h => by
      simp only [isBoxed, sumHead, tier_mu] at h
      exact vsh_zero t (by simpa [isBoxed] using h)
  | .iex t, h => by
      simp only [isBoxed, sumHead, tier_iex] at h
      simp only [shp, vsh, vsh_zero t (by simpa [isBoxed] using h)]
  | .tex κ t, h => by
      simp only [isBoxed, sumHead, tier_tex] at h
      simp only [shp, vsh, vsh_zero t (by simpa [isBoxed] using h)]
  | .iall t, h => by
      simp only [isBoxed, sumHead, tier_iall] at h
      exact vsh_zero t (by simpa [isBoxed] using h)
  | .intS _, h | .int, h | .fix _ _, h | .lanes _ _, h | .prod _ _, h | .code _ _, h | .tvar _, h
  | .ptr _ _, h | .ptrOpt _ _, h | .loc _ _, h | .unit, h | .void, h | .array _ _, h | .share _, h
  | .cap _ _, h | .word _ _, h | .tok _ _, h | .word2 _ _, h | .tok2 _ _ _ _, h | .epair _ _, h | .tokE _ _ _, h => by simp [isBoxed, sumHead] at h

/-- (T3c-5d) **Re-boxing** under a coherent view (`VR_ren0` through `VR_close`). -/
theorem VR_ren {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {t : Ty} {R : Shp} {s1 s2 : Nat}
    {w1 w2 : Word} {x1 x2 : WeakMem.Address} {B1 B2 : Box}
    (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (ho2 : x2.offset = 0)
    (hb1 : η.box x1.label = some B1) (hb2 : η.box x2.label = some B2) (hs : η.sto x1.label = none)
    (hi : η.ini x1.label ≤ η.ini x2.label) (ht : B1.tag + s2 = B2.tag + s1) (hpay : WLe B1.pay B2.pay)
    (hm : BoxSeen η x2.label B2 ∨ B2.fr ≤ w2.view) (hR : bh R)
    (h : VR ρ η t (vsh s1 R) [w1]) (hri : min (η.ini x1.label) (η.rini x1.label) ≤ η.rini x2.label) : VR ρ η t (vsh s2 R) [w2] := by
  have c := fun S ws => VR_close hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  exact (c _ _).2 (VR_ren0 w1 w2 x1 x2 B1 B2 h1 h2 ho2 hpay _ (CE η) ρ R s1 s2 ht (fun _ _ _ h => h) hR
    hb1 hb2 hs hi hri hm ((c _ _).1 h))



/-- (T3c-5d) A memory value is a value in the thread's view (coherent `η`). -/
theorem VR_seen {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {t : Ty} {S : Shp} {ws : List Word}
    (h : VR ρ η.unsee t S ws) : VR ρ η t S ws := by
  have c1 := VR_close hc.unsee ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c2 := VR_close hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  refine c2.2 ?_
  have h1 : VR ρ (CE η.unsee) (cl ρ η.wit 0 0 t) S ws := c1.1 h
  exact VR_mono _ (CE η.unsee) (CE η) ρ S ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h1

/-- (T3c-5d) A value whose pointers are viewed at least `V`, when every `seen`
label's frontier is at most `V`, is a memory value (coherent `η`). -/
theorem VR_store {η : TEnv} (hc : Coh η) {V : WeakMem.Ts} {ρ : Nat → Nat} {t : Ty} {S : Shp}
    {ws : List Word} (hS : ∀ l, η.seen l → ∃ f, η.pfr l = some f ∧ f ≤ V) (hL : LocAbove V ws)
    (h : VR ρ η t S ws) : VR ρ η.unsee t S ws := by
  have c1 := VR_close hc.unsee ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c2 := VR_close hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  refine c1.2 ?_
  exact VR_unsee V _ (CE η) (CE η.unsee) ρ S ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
    (fun _ _ h => h) hL (c2.1 h)

theorem accs_of_rawWords {a : Ty} {k : Nat} (h : a.rawWords = some k) :
    ∃ us, accs a = some us ∧ nWords us = k := by
  simp only [Ty.rawWords, Ty.width] at h
  cases hw : (info Ty.top a).width with
  | none => rw [hw] at h; cases h
  | some w =>
      rw [hw, Option.bind_some] at h
      cases ha : accs a with
      | none => rw [accs_none_width a ha] at hw; cases hw
      | some us => exact ⟨us, rfl, accs_width a us ha w k hw h⟩

theorem isBoxed_lnorm (t : Ty) : isBoxed (lnorm t) = isBoxed t := by
  simp only [isBoxed, sumHead_lnorm, tier_lnorm]

theorem wc_boxed {a b : Ty} (hS : (Ty.sum a b).tier = .boxed) : wc (Ty.sum a b) = some 1 := by
  simp [wc, accs, hS, nWords, Acc.size]

theorem tier_lsum {a b : Ty} (hS : (Ty.sum a b).tier = .boxed) : (Ty.sum (lnorm a) (lnorm b)).tier = .boxed := by
  rw [show Ty.sum (lnorm a) (lnorm b) = lnorm (.sum a b) from rfl, tier_lnorm]; exact hS

/-- (T3c-5d) An arm's word count, at the layout normal form. -/
theorem armsWc_lnorm {Ra Rb : Ty} {k n : Nat} (h : ((armsOf (.sum Ra Rb))[k]?).bind wc = some n) :
    ((armsOf (.sum (lnorm Ra) (lnorm Rb)))[k]?).bind wc = some n := by
  rw [show Ty.sum (lnorm Ra) (lnorm Rb) = lnorm (.sum Ra Rb) from rfl, armsOf_lnorm, List.getElem?_map]
  cases e : (armsOf (.sum Ra Rb))[k]? with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; simpa [wc_lnorm] using h

/-! ### (T3c-5d, β1) `VR` gives validity at `∀`-free types -/

/-- Validity survives layout normalisation (`Ptr ≤ Ptr?`). -/
theorem Valid_lnorm : ∀ (t : Ty) (ws : List Word), Valid t ws → Valid (lnorm t) ws := by
  intro t
  induction t with
  | ptr μ u _ => intro ws h; simp only [lnorm, Valid] at h ⊢; exact Or.inr h
  | ptrOpt μ u _ => intro ws h; simpa only [lnorm, Valid] using h
  | loc μ u _ => intro ws h; simpa only [lnorm, Valid] using h
  | prod a b iha ihb =>
      intro ws h; simp only [lnorm, Valid, wc_lnorm] at h ⊢
      intro n hn; exact ⟨iha _ (h n hn).1, ihb _ (h n hn).2⟩
  | sum a b iha ihb =>
      intro ws h; simp only [lnorm, Valid] at h ⊢
      exact SumV_mono (tier_lnorm (.sum a b)).symm (arms_lnorm a) (arms_lnorm b)
        (sumHead_lnorm a).symm (sumHead_lnorm b).symm (tier_lnorm a).symm (tier_lnorm b).symm
        (wc_lnorm a).symm (wc_lnorm b).symm (iha) (ihb) h
  | void => intro ws h; simp [Valid] at h
  | refine t ψ ih => intro ws h; simp only [lnorm, Valid] at h ⊢; exact ih _ h
  | iall t ih => intro ws h; simp only [lnorm, Valid] at h ⊢; exact ih _ h
  | iex t ih => intro ws h; simp only [lnorm, Valid] at h ⊢; exact ih _ h
  | mu t ih => intro ws h; simp only [lnorm, Valid] at h ⊢; exact ih _ h
  | tex κ t ih => intro ws h; simp only [lnorm, Valid] at h ⊢; exact ih _ h
  | _ => intro ws _; simp [lnorm, Valid]

/-- A pointer arm's payload is not `null` (what decoding at `Ptr?` cannot rule out). -/
def NoNull (as : List Ty) (j : Nat) (p : List Word) : Prop :=
  ∀ a w, as[j]? = some a → armK a = .ptr → p = [w] → w.val ≠ .null

theorem get_back {as bs : List Ty} (h : ArmsLe as bs) {j : Nat} {b : Ty}
    (hb : bs[j]? = some b) : ∃ a, as[j]? = some a ∧ ArmLe a b := by
  induction h generalizing j with
  | nil => simp at hb
  | cons hab _ ih =>
      cases j with
      | zero => simp at hb; subst hb; exact ⟨_, rfl, hab⟩
      | succ j => simp at hb; exact ih hb

/-- **Decoding back**: what decodes at `Ptr?` decodes the same at `Ptr`, unless
it is a `null` there. -/
theorem decodeArm_back {tr : Tier} {as bs : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : ArmsLe as bs) (hd : decodeArm tr bs ws = some (j, p)) (hn : NoNull as j p) :
    decodeArm tr as ws = some (j, p) := by
  cases tr with
  | boxed => simp [decodeArm] at hd
  | niche =>
      match ws, hd with
      | [w], hd =>
          simp only [decodeArm] at hd ⊢
          cases hw : w.val with
          | loc a g =>
              rw [hw] at hd
              have e := congrArg (fun l => l[g]?) (ptrIdx_mono h 0)
              simp only [List.getElem?_map] at e
              cases h2 : ((enumFrom bs 0).filter (fun p => isPtrish p.2))[g]? with
              | none => simp [h2, bind, Option.bind] at hd
              | some pr' =>
                  cases h1 : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
                  | none => simp [h1, h2] at e
                  | some pr =>
                      simp [h1, h2] at e
                      simp only [h2, bind, Option.bind] at hd
                      simp only [h1, bind, Option.bind]
                      rw [e]; exact hd
          | num k =>
              rw [hw] at hd
              cases h2 : bs[k]? with
              | none => simp [h2, bind, Option.bind] at hd
              | some b =>
                  obtain ⟨a, h1, hab⟩ := get_back h h2
                  simp only [h2, bind, Option.bind] at hd
                  simp only [h1, bind, Option.bind]
                  rcases hab.1 with e | ⟨e1, e2⟩
                  · rw [e]; exact hd
                  · rw [e2] at hd; simp [pure] at hd
                    obtain ⟨rfl, rfl⟩ := hd
                    exact absurd rfl (hn a _ h1 e1 rfl)
          | _ => rw [hw] at hd; simp at hd
      | [], hd => simp [decodeArm] at hd
      | _ :: _ :: _, hd => simp [decodeArm] at hd
  | wide =>
      match ws, hd with
      | [t, w], hd =>
          simp only [decodeArm] at hd ⊢
          cases ht : t.val with
          | num k =>
              rw [ht] at hd
              cases h2 : bs[k]? with
              | none => simp [h2, bind, Option.bind] at hd
              | some b =>
                  obtain ⟨a, h1, hab⟩ := get_back h h2
                  simp only [h2, bind, Option.bind] at hd
                  simp only [h1, bind, Option.bind, hab.2]
                  exact hd
          | _ => rw [ht] at hd; simp at hd
      | [], hd => simp [decodeArm] at hd
      | [_], hd => simp [decodeArm] at hd
      | _ :: _ :: _ :: _, hd => simp [decodeArm] at hd

/-- **Encoding back**, likewise. -/
theorem encodeArm_back {tr : Tier} {as bs : List Ty} {j : Nat} {p q : List Word}
    (h : ArmsLe as bs) (he : encodeArm tr bs j p = some q) (hn : NoNull as j p) :
    encodeArm tr as j p = some q := by
  cases tr with
  | niche =>
      simp only [encodeArm, bind, Option.bind] at he ⊢
      cases h2 : bs[j]? with
      | none => simp [h2] at he
      | some b =>
          obtain ⟨a, h1, hab⟩ := get_back h h2
          simp only [h2] at he
          simp only [h1, slot_mono h j]
          rcases hab.1 with e | ⟨e1, e2⟩
          · rw [e]; exact he
          · rw [e2] at he; rw [e1]
            match p, he with
            | [w], he =>
                simp only at he ⊢
                split at he
                · exact he
                · rename_i hw; exact absurd hw (hn a w h1 e1 rfl)
                · simp at he
  | wide => exact he
  | boxed => simp [encodeArm] at he

theorem PayOK_back {a b : Ty} {p : List Word} (hab : ArmLe a b) (h : PayOK b p)
    (hn : armK a = .ptr → ∀ w, p = [w] → w.val ≠ .null) : PayOK a p := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hab.2 ▸ h1, fun hk => ?_, fun hk => ?_⟩
  · rcases hab.1 with e | ⟨_, e2⟩
    · exact h2 (e.symm.trans hk)
    · obtain ⟨w, rfl, hw⟩ := h3 e2
      rcases hw with hw | ⟨adr, hw⟩
      · exact absurd hw (hn hk w rfl)
      · exact ⟨w, adr, rfl, hw⟩
  · rcases hab.1 with e | ⟨e1, _⟩
    · exact h3 (e.symm.trans hk)
    · rw [e1] at hk; simp at hk

theorem ptr_of_armK {x : Ty} (hA : Atom x) (h : armK x = .ptr) : ∃ μ u, x = .ptr μ u := by
  have e := armK_ptr h
  cases x <;> simp only [Atom] at hA
  case ptr μ u => exact ⟨μ, u, rfl⟩
  all_goals first
    | (have h' := congrArg Arms.ptrs e; simp [info, Info.leaf, leaf_ptrs, Arms.ptrArm] at h'; done)
    | (have h' := congrArg Arms.units e; simp [info, Arms.ptrArm, Arms.optArm] at h'; done)

/-- A valid value of a non-sum type whose arm is a pointer is a pointer. -/
theorem Valid_ptrspine : ∀ (a : Ty) (q : List Word) (x : Ty), sumHead a = false →
    (armsOf a)[0]? = some x → armK x = .ptr → Valid a q → ∃ w adr, q = [w] ∧ w.val = .loc adr 0 := by
  intro a
  induction a with
  | sum => intro q x hs; simp [sumHead] at hs
  | void => intro q x _ hx; simp [armsOf] at hx
  | refine t ψ ih => intro q x hs hx hk hv; exact ih q x hs hx hk hv
  | iall t ih => intro q x hs hx hk hv; exact ih q x hs hx hk hv
  | iex t ih => intro q x hs hx hk hv; exact ih q x hs hx hk hv
  | mu t ih => intro q x hs hx hk hv; exact ih q x hs hx hk hv
  | tex κ t ih => intro q x hs hx hk hv; exact ih q x hs hx hk hv
  | ptr μ u _ =>
      intro q x _ _ _ hv
      simp only [Valid] at hv
      obtain ⟨ad, had⟩ := hv
      obtain ⟨w, rfl, hw⟩ := map_singleton had
      exact ⟨w, ad, rfl, hw⟩
  | _ =>
      intro q x _ hx hk _
      simp only [armsOf, List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      obtain ⟨μ, u, e⟩ := ptr_of_armK (by simp [Atom]) hk
      cases e

theorem rawWords_popt : (Ty.ptrOpt .pub .unit).rawWords = some 1 := by
  decide

theorem armK_popt : armK (Ty.ptrOpt .pub .unit) = .opt := by
  simp [armK, info, Arms.ptrArm, Arms.optArm]

/-- **No hidden `null`**: a valid value, built at the layout normal form from a
`null` payload, is not at a pointer arm. -/
theorem null_arm {a x : Ty} {j : Nat} {w : Word} {q : List Word} (hv : Valid a q) (hs : ShapeC a q)
    (hb : isBoxed a = false) (hx : (armsOf a)[j]? = some x) (hk : armK x = .ptr)
    (ho : ofArm (lnorm a) j [w] = some q) (hn : w.val = .null) : False := by
  cases hsh : sumHead a with
  | false =>
      unfold ofArm at ho
      rw [sumHead_lnorm, hsh] at ho
      simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at ho
      split at ho
      · rename_i hj; subst hj; simp only [Option.some.injEq] at ho; subst ho
        obtain ⟨w', adr, e, hw'⟩ := Valid_ptrspine a [w] x hsh hx hk hv
        simp only [List.cons.injEq, and_true] at e; subst e
        rw [hn] at hw'; cases hw'
      · simp at ho
  | true =>
      have ht : a.tier ≠ .boxed := by intro e; simp [isBoxed, hsh, e] at hb
      obtain ⟨j2, p2, arm2, ha, harm, hp, -⟩ := asArm_valid a q hv hs ht
      have ha' := asArm_lnorm ha
      have hA := atom_of_mem a x (List.mem_of_getElem? hx)
      obtain ⟨μ, u, rfl⟩ := ptr_of_armK hA hk
      have hxl : (armsOf (lnorm a))[j]? = some (Ty.ptrOpt .pub .unit) := by
        rw [armsOf_lnorm, List.getElem?_map, hx]; rfl
      have hpl : PayOK (Ty.ptrOpt .pub .unit) [w] := by
        refine ⟨rawWords_popt, fun h => ?_, fun _ => ⟨w, rfl, Or.inl hn⟩⟩
        rw [armK_popt] at h; cases h
      unfold ofArm at ho
      rw [sumHead_lnorm, hsh, if_pos rfl] at ho
      obtain ⟨p', hd, e⟩ := roundtrip (by rw [tier_lnorm]; exact ht) hxl hpl ho
      unfold asArm at ha'
      rw [sumHead_lnorm, hsh, if_pos rfl, hd] at ha'
      simp only [Option.some.injEq, Prod.mk.injEq] at ha'
      obtain ⟨rfl, rfl⟩ := ha'
      rw [hx] at harm; simp only [Option.some.injEq] at harm; subst harm
      obtain ⟨w', adr, rfl, hw'⟩ := hp.2.1 hk
      obtain ⟨w'', e1, e2⟩ := veq_one e
      simp only [List.cons.injEq, and_true] at e1; subst e1
      rw [e2, hn] at hw'; cases hw'

/-- **Building back**: what the layout normal form builds, the runtime type
builds too, unless it is a `null` at a pointer arm. -/
theorem ofArm_back {a : Ty} {j : Nat} {p q : List Word} (ho : ofArm (lnorm a) j p = some q)
    (hn : NoNull (armsOf a) j p) : ofArm a j p = some q := by
  unfold ofArm at ho ⊢
  rw [sumHead_lnorm, tier_lnorm] at ho
  split at ho
  · rename_i hs; rw [if_pos hs]; exact encodeArm_back (arms_lnorm a) ho hn
  · rename_i hs; rw [if_neg hs]; exact ho

theorem isBoxed_false {t : Ty} (h : t.tier ≠ .boxed) : isBoxed t = false := by
  simp [isBoxed, h]

/-- **`VR` gives validity**, given validity at the layout
normal form (which keeps pointer offsets and padding canonical; without it the
claim fails at a wide sum with a niche summand). -/
theorem Valid_of_VR : ∀ (T : Ty) (η : TEnv) (ρ : Nat → Nat) (ws : List Word),
    (∀ k S ws, ¬ η.rels k S ws) → Valid (lnorm T) ws → VR ρ η T (shp T) ws → Valid T ws := by
  intro T
  induction T with
  | ptr μ u _ =>
      intro η ρ ws _ _ h; simp only [VR] at h; simp only [Valid]
      obtain ⟨a, c, h, -⟩ := h; exact ⟨a, h⟩
  | ptrOpt μ u _ =>
      intro η ρ ws _ _ h; simp only [VR] at h; simp only [Valid]
      rcases h with h | ⟨a, c, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, h⟩
  | loc μ u _ =>
      intro η ρ ws _ _ h; simp only [VR] at h; simp only [Valid]
      rcases h with ⟨h, -⟩ | ⟨a, c, _, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, h⟩
  | void => intro η ρ ws _ _ h; simp [VR] at h
  | iall t ih =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid] at hl
      exact ih η (vcons 0 ρ) ws hr hl (h 0)
  | refine t ψ ih =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm] at hl
      exact ih η ρ ws hr hl h.1
  | mu b ih =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid] at hl
      exact ih _ ρ ws (fun k S ws hk => by
        cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
        | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)) hl h
  | tex κ b ih =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid] at hl
      obtain ⟨n, rb, s, hrt, -, -, h⟩ := h
      simp only [Shp.tex.injEq] at hrt; obtain ⟨-, rfl⟩ := hrt
      exact ih _ ρ ws (fun k S ws hk => by
        cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
        | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)) hl h
  | iex b ih =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid] at hl
      obtain ⟨n, rb, w, hrt, h⟩ := h
      simp only [Shp.iex.injEq] at hrt; obtain ⟨-, rfl⟩ := hrt
      exact ih η _ ws hr hl h
  | prod a b iha ihb =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid, wc_lnorm] at hl
      obtain ⟨ra, rb, hrt, h⟩ := h
      simp only [Shp.prod.injEq] at hrt; obtain ⟨rfl, rfl⟩ := hrt
      intro n hn
      have h' := h n (by rw [shp_wc]; exact hn)
      exact ⟨iha η ρ _ hr (hl n hn).1 h'.2.1, ihb η ρ _ hr (hl n hn).2 h'.2.2⟩
  | sum a b iha ihb =>
      intro η ρ ws hr hl h
      simp only [Valid]; simp only [shp, VR] at h; simp only [lnorm, Valid] at hl
      obtain ⟨n, Ra, Rb, hrt, h⟩ := h
      simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hrt; obtain ⟨-, rfl, rfl⟩ := hrt
      have et : (Ty.sum (lnorm a) (lnorm b)).tier = (Ty.sum a b).tier := tier_lnorm (.sum a b)
      have hAL : ArmsLe (armsOf (.sum a b)) (armsOf (.sum (lnorm a) (lnorm b))) := arms_lnorm (.sum a b)
      have la : (armsOf (lnorm a)).length = (armsOf a).length := by rw [armsOf_lnorm, List.length_map]
      by_cases htb : (Ty.sum a b).tier = .boxed
      · exact Or.inl htb
      obtain ⟨hta, htb'⟩ := tier_sum htb
      rcases h with ⟨hbx, -⟩ | ⟨j, p, hd, hA, hB⟩
      · rw [et] at hbx; exact absurd hbx htb
      rcases hl with hbx | ⟨j', p', arm', hd', harm', hp', ⟨q0, hq0, eq0⟩, hA', hB'⟩
      · rw [et] at hbx; exact absurd hbx htb
      rw [hd] at hd'; simp only [Option.some.injEq, Prod.mk.injEq] at hd'; obtain ⟨rfl, rfl⟩ := hd'
      have hqa : j < (armsOf a).length → ∃ q, ofArm (lnorm a) j p = some q ∧ ShapeC a q ∧
          wc a ≠ none ∧ Valid a q := by
        intro hj
        obtain ⟨q, hq, hs, hw, hv⟩ := hA' (by rw [la]; exact hj)
        obtain ⟨q', hq', hvr⟩ := hA (by rw [la]; exact hj)
        rw [hq] at hq'; simp only [Option.some.injEq] at hq'; subst hq'
        refine ⟨q, hq, ShapeC_wc (wc_lnorm a) hs, by rw [← wc_lnorm]; exact hw, ?_⟩
        exact iha η ρ q hr hv (by rw [← shp_lnorm]; exact hvr)
      have hqb : (armsOf a).length ≤ j → ∃ q, ofArm (lnorm b) (j - (armsOf a).length) p = some q ∧
          ShapeC b q ∧ wc b ≠ none ∧ Valid b q := by
        intro hj
        obtain ⟨q, hq, hs, hw, hv⟩ := hB' (by rw [la]; exact hj)
        obtain ⟨q', hq', hvr⟩ := hB (by rw [la]; exact hj)
        rw [la] at hq hq'
        rw [hq] at hq'; simp only [Option.some.injEq] at hq'; subst hq'
        refine ⟨q, hq, ShapeC_wc (wc_lnorm b) hs, by rw [← wc_lnorm]; exact hw, ?_⟩
        exact ihb η ρ q hr hv (by rw [← shp_lnorm]; exact hvr)
      have hnn : NoNull (armsOf (.sum a b)) j p := by
        intro x w hx hk hp hnl
        subst hp
        simp only [armsOf] at hx
        by_cases hj : j < (armsOf a).length
        · rw [List.getElem?_append_left hj] at hx
          obtain ⟨q, hq, hs, -, hv⟩ := hqa hj
          exact null_arm hv hs (isBoxed_false hta) hx hk hq hnl
        · rw [List.getElem?_append_right (by omega)] at hx
          obtain ⟨q, hq, hs, -, hv⟩ := hqb (by omega)
          exact null_arm hv hs (isBoxed_false htb') hx hk hq hnl
      have hnn_a : j < (armsOf a).length → NoNull (armsOf a) j p := by
        intro hj x w hx; apply hnn x w
        simp only [armsOf]; rw [List.getElem?_append_left hj]; exact hx
      have hnn_b : (armsOf a).length ≤ j → NoNull (armsOf b) (j - (armsOf a).length) p := by
        intro hj x w hx; apply hnn x w
        simp only [armsOf]; rw [List.getElem?_append_right hj]; exact hx
      obtain ⟨x, hx, hxa⟩ := get_back hAL harm'
      rw [et] at hd hq0
      refine Or.inr ⟨j, p, x, decodeArm_back hAL hd hnn, hx,
        PayOK_back hxa hp' (fun hk w hp hnl => hnn x w hx hk hp hnl),
        ⟨q0, encodeArm_back hAL hq0 hnn, eq0⟩, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, hq, hs, hw, hv⟩ := hqa hj
        exact ⟨q, ofArm_back hq (hnn_a hj), hs, hw, hv⟩
      · obtain ⟨q, hq, hs, hw, hv⟩ := hqb hj
        exact ⟨q, ofArm_back hq (hnn_b hj), hs, hw, hv⟩
  | _ => intros; simp [Valid]

/-- (T3c-5d) **A fresh box, left arm**: a reference to an own box whose tag
selects an unboxed left summand, its payload a value there (as not yet seen). -/
theorem VR_boxL {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    {q : List Word} (hS : (Ty.sum Ra Rb).tier = .boxed) (hRa : isBoxed Ra = false)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : B.tag < (armsOf Ra).length) (hq : ofArm Ra B.tag B.pay = some q) (hv : VR ρ η.unsee a (shp Ra) q)
    (hs : ShapeC Ra q) (hwc : wc Ra ≠ none) (hvd : Valid Ra q)
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    VR ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun _ => ⟨fun h => ?_, fun _ => ?_⟩, fun h => ?_⟩⟩
  · rw [isBoxed_lnorm] at h; rw [hRa] at h; cases h
  · exact ⟨q, by rw [Nat.sub_zero]; exact ofArm_lnorm hq, ShapeC_wc (wc_lnorm Ra).symm hs,
      by rw [wc_lnorm]; exact hwc, Valid_lnorm _ _ hvd, by rw [shp_lnorm]; exact hv⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega

/-- (T3c-5d) **A fresh box, right arm.** -/
theorem VR_boxR {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    {q : List Word} (hS : (Ty.sum Ra Rb).tier = .boxed) (hRb : isBoxed Rb = false)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : (armsOf Ra).length ≤ B.tag) (hq : ofArm Rb (B.tag - (armsOf Ra).length) B.pay = some q)
    (hv : VR ρ η.unsee b (shp Rb) q) (hs : ShapeC Rb q) (hwc : wc Rb ≠ none) (hvd : Valid Rb q)
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    VR ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun h => ?_, fun _ => ⟨fun h => ?_, fun _ => ?_⟩⟩⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega
  · rw [isBoxed_lnorm] at h; rw [hRb] at h; cases h
  · refine ⟨q, ?_, ShapeC_wc (wc_lnorm Rb).symm hs, by rw [wc_lnorm]; exact hwc, Valid_lnorm _ _ hvd,
      by rw [shp_lnorm]; exact hv⟩
    rw [Nat.sub_zero, armsOf_lnorm, List.length_map]; exact ofArm_lnorm hq

/-- (T3c-5d) A boxed sum's reference is laid out at the sum. -/
theorem Lay_box {σs : List Ty} {t τ rt : Ty} {ws : List Word} {w : Word} (hl : Lay σs t rt ws)
    (hS : (Ty.sum rt (close σs τ)).tier = .boxed) :
    Lay σs (.sum t τ) (.sum rt (close σs τ)) [w] := by
  obtain ⟨-, hsk, -, -, hly⟩ := hl
  refine ⟨fun us hu => by
      have hw := wc_boxed hS; simp only [wc, hu, Option.map_some, Option.some.injEq] at hw; simp [hw], ?_, wc_sum_ne _ _, Or.inl hS,
    by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
  show Ty.sum (etok (skel rt)) (etok (skel (close σs τ))) = _
  rw [hsk]; rfl

/-- (T3c-5d) The arms of a boxed shape's head sum. -/
def headArms : Shp → Option (List Ty)
  | .sum _ (.sum Ra Rb) => some (armsOf (.sum Ra Rb))
  | .iex _ b => headArms b
  | .tex _ b => headArms b
  | _ => none

/-- (T3c-5d) A sum under refinements, `μ`, existentials and (T3c-5f) index
`∀`s: what `sumHead` sees (`sumSpine_of_isBoxed`). -/
def sumSpine : Ty → Prop
  | .refine t _ | .mu t | .iex t | .tex _ t | .iall t => sumSpine t
  | .sum _ _ => True
  | _ => False

theorem sumSpine_er : ∀ t : Ty, sumSpine (er t) ↔ sumSpine t := by
  intro t; induction t <;> simp_all [er, sumSpine]

theorem sumSpine_int : ∀ t : Ty, skel t = .int → ¬ sumSpine t := by
  intro t
  induction t with
  | refine t ψ ih =>
      intro h
      simp only [skel] at h
      cases hs : skel t with
      | int => exact ih hs
      | _ => rw [hs] at h; simp [rf] at h
  | _ => intro h; simp_all [skel, sumSpine]

theorem sumSpine_sig : ∀ t : Ty, sumSpine (sig t) ↔ sumSpine t := by
  intro t
  induction t with
  | refine t ψ ih =>
      simp only [sig, skel] at ih ⊢
      cases h : skel t with
      | int =>
          have := sumSpine_int t h
          simp [rf, er, sumSpine, this]
      | _ => simp_all [rf, er, sumSpine]
  | _ => simp_all [sig, skel, er, sumSpine]

/-- (T3c-5f) A boxed type is a sum spine: `sumHead` looks through exactly the
binders `sumSpine` does. -/
theorem sumSpine_of_sumHead : ∀ t : Ty, sumHead t = true → sumSpine t := by
  intro t; induction t <;> simp_all [sumHead, sumSpine]

theorem sumSpine_of_isBoxed (t : Ty) (h : isBoxed t = true) : sumSpine t :=
  sumSpine_of_sumHead t (by simp only [isBoxed, Bool.and_eq_true] at h; exact h.1)

/-- (T3c-5d) **What a boxed value is**, in a view with no type-variable
relations: a reference to a box, whose tag (less the offset) indexes an arm of
the head sum with as many words as the payload. -/
theorem VR_boxE0 (ws : List Word) :
    ∀ (t : Ty) (η : TEnv) (ρ : Nat → Nat) (R : Shp) (s : Nat),
      (∀ k S ws, ¬ η.rels k S ws) → bh R → sumSpine t → VR ρ η t (vsh s R) ws →
      ∃ w x B as, ws = [w] ∧ w.val = .loc x 0 ∧ x.offset = 0 ∧ η.box x.label = some B ∧ s ≤ B.tag ∧
        headArms R = some as ∧ (as[B.tag - s]?).bind wc = some B.pay.length ∧
        (BoxSeen η x.label B ∨ B.fr ≤ w.view) := by
  intro t
  induction t with
  | refine t ψ ih =>
      intro η ρ R s hr hR hs h
      exact ih η ρ R s hr hR hs h.1
  | mu b ih =>
      intro η ρ R s hr hR hs h
      simp only [VR] at h
      have := ih _ ρ R s (fun k S ws hk => by
        cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
        | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)) hR hs h
      simpa [BoxSeen, TEnv.push0, TEnv.ins, TEnv.insR] using this
  | iex b ih =>
      intro η ρ R s hr hR hs h
      simp only [VR] at h
      obtain ⟨n, rb, w', hrt, h⟩ := h
      cases R with
      | iex m R0 =>
          simp only [vsh, Shp.iex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          exact ih η _ R0 s hr (by simpa [bh] using hR) hs h
      | _ => simp [vsh] at hrt
  | tex κ b ih =>
      intro η ρ R s hr hR hs h
      simp only [VR] at h
      obtain ⟨n, rb, s', hrt, -, -, h⟩ := h
      cases R with
      | tex m R0 =>
          simp only [vsh, Shp.tex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          have := ih _ ρ R0 s (fun k S ws hk => by
            cases k with
            | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
            | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk))
            (by simpa [bh] using hR) hs h
          simpa [BoxSeen, TEnv.push0, TEnv.ins, TEnv.insR, headArms] using this
      | _ => simp [vsh] at hrt
  | iall b ih =>
      intro η ρ R s hr hR hs h
      simp only [VR] at h
      exact ih η _ R s hr hR hs (h 0)
  | sum a b _ _ =>
      intro η ρ R s hr hR _ h
      simp only [VR] at h
      obtain ⟨n, Ra, Rb, hrt, h⟩ := h
      cases R with
      | sum m R0 =>
          simp only [vsh, Shp.sum.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          simp only [bh] at hR
          rcases h with ⟨-, x, s', B, hw, ho, hb, hn, ⟨hsB, hwa⟩, hmo, -, -⟩ | ⟨j, p, hd, _, _⟩
          · obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
              rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
              · simp at hw
              · exact ⟨w, rfl⟩
              · simp at hw
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hw
            have hn' : s' = s := by simp at hn; omega
            subst hn'
            refine ⟨w, x, B, _, rfl, hw, ho, hb, hsB, rfl, hwa, ?_⟩
            rcases hmo with hmo | hmo
            · exact Or.inl hmo
            · exact Or.inr (hmo w (List.mem_singleton_self _))
          · rw [hR] at hd; simp [decodeArm] at hd
      | _ => simp [vsh] at hrt
  | _ => intro η ρ R s hr hR hs h; simp [sumSpine] at hs

theorem headArms_shp : ∀ t : Ty, sumSpine t → headArms (shp t) = some ((armsOf t).map lnorm)
  | .sum a b, _ => by simp only [shp, lnorm, headArms]; rw [← armsOf_lnorm]; rfl
  | .refine t _, h => headArms_shp t h
  | .mu t, h => headArms_shp t h
  | .iex t, h => headArms_shp t h
  | .tex _ t, h => headArms_shp t h
  | .iall t, h => headArms_shp t h
  | .intS _, h | .int, h | .fix _ _, h | .lanes _ _, h | .prod _ _, h | .code _ _, h | .tvar _, h
  | .ptr _ _, h | .ptrOpt _ _, h | .loc _ _, h | .unit, h | .void, h | .array _ _, h | .share _, h
  | .cap _ _, h | .word _ _, h | .tok _ _, h | .word2 _ _, h | .tok2 _ _ _ _, h | .epair _ _, h | .tokE _ _ _, h => by simp [sumSpine] at h

/-- (T3c-5d) **What a boxed value is** (coherent `η`). -/
theorem VR_boxE {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {t : Ty} {R : Shp} {s : Nat} {ws : List Word}
    (hR : bh R) (hs : sumSpine (cl ρ η.wit 0 0 t)) (h : VR ρ η t (vsh s R) ws) :
    ∃ w x B as, ws = [w] ∧ w.val = .loc x 0 ∧ x.offset = 0 ∧ η.box x.label = some B ∧ s ≤ B.tag ∧
      headArms R = some as ∧ (as[B.tag - s]?).bind wc = some B.pay.length ∧
      (BoxSeen η x.label B ∨ B.fr ≤ w.view) := by
  have c := VR_close hc ρ t [] 0 ρ ρ (vsh s R) ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  exact VR_boxE0 ws _ (CE η) ρ R s (fun _ _ _ h => h) hR hs (c.1 h)


theorem rawWords_iex_inner {t : Ty} {k : Nat} (h : (Ty.iex t).rawWords = some k) :
    ∃ w0, (info Ty.top t).width = some w0 ∧ w0.closed = some k := by
  simp only [Ty.rawWords, Ty.width, info, top_shiftI] at h
  cases hw : lowerW (info Ty.top t).width with
  | none => rw [hw] at h; cases h
  | some w =>
      rw [hw, Option.bind_some] at h
      obtain ⟨w0, e, ec⟩ := lowerW_some hw
      exact ⟨w0, e, ec ▸ h⟩

theorem rawWords_tex_inner {κ : Kind} {t : Ty} {k : Nat} (h : (Ty.tex κ t).rawWords = some k) :
    ∃ w0, (info Ty.top t).width = some w0 ∧ w0.closed = some k := by
  simp only [Ty.rawWords, Ty.width, info, top_cons] at h
  cases hw : (info Ty.top t).width with
  | none => rw [hw] at h; cases h
  | some w => rw [hw, Option.bind_some] at h; exact ⟨w, rfl, h⟩

theorem accs_inner {t : Ty} {k : Nat} (h : ∃ w0, (info Ty.top t).width = some w0 ∧ w0.closed = some k) :
    ∃ us, accs t = some us ∧ nWords us = k := by
  obtain ⟨w0, hw, hk⟩ := h
  cases ha : accs t with
  | none => rw [accs_none_width t ha] at hw; cases hw
  | some us => exact ⟨us, rfl, accs_width t us ha w0 k hw hk⟩

/-- (T3c-5d) A non-sum-headed valid type is a one-arm sum whose arm has the
same access width. -/
theorem accs_spine : ∀ (rt : Ty) (ws : List Word), sumHead rt = false → Valid rt ws →
    ∀ us, accs rt = some us → ∃ a us', armsOf rt = [a] ∧ accs a = some us' ∧ nWords us' = nWords us := by
  intro rt
  induction rt with
  | sum a b _ _ => intro ws h; simp [sumHead] at h
  | void => intro ws _ hv; exact hv.elim
  | refine t ψ ih => intro ws hs hv us h; exact ih ws hs hv us h
  | iall t ih => intro ws hs hv us h; exact ih ws hs hv us h
  | mu t ih => intro ws hs hv us h; exact ih ws hs hv us h
  | iex t ih =>
      intro ws hs hv us h
      rcases accs_iex t with e | ⟨k, hk, ek⟩
      · rw [e] at h; exact ih ws hs hv us h
      · rw [h, Option.map_some, Option.some.injEq] at ek
        obtain ⟨us0, h0, n0⟩ := accs_inner (rawWords_iex_inner hk)
        obtain ⟨a, us', ha, hu, hn⟩ := ih ws hs hv us0 h0
        exact ⟨a, us', ha, hu, by rw [hn, n0, ek]⟩
  | tex κ t ih =>
      intro ws hs hv us h
      rcases accs_tex κ t with e | ⟨k, hk, ek⟩
      · rw [e] at h; exact ih ws hs hv us h
      · rw [h, Option.map_some, Option.some.injEq] at ek
        obtain ⟨us0, h0, n0⟩ := accs_inner (rawWords_tex_inner hk)
        obtain ⟨a, us', ha, hu, hn⟩ := ih ws hs hv us0 h0
        exact ⟨a, us', ha, hu, by rw [hn, n0, ek]⟩
  | _ => intro ws _ _ us h; exact ⟨_, us, rfl, h, rfl⟩

/-- (T3c-5d) `asArm` at a valid operand that is not a boxed sum: its arm, with
accesses fitting the payload. -/
theorem asArm_box (rt : Ty) (ws : List Word) (hv : Valid rt ws) (hs : ShapeC rt ws) (hw : wc rt ≠ none)
    (hb : isBoxed rt = false) :
    ∃ j p arm us, asArm rt ws = some (j, p) ∧ (armsOf rt)[j]? = some arm ∧ accs arm = some us ∧
      nWords us = p.length ∧ ∃ q, ofArm rt j p = some q ∧ VEq q ws := by
  cases hsh : sumHead rt with
  | true =>
      have ht : rt.tier ≠ .boxed := by intro e; simp [isBoxed, hsh, e] at hb
      obtain ⟨j, p, arm, ha, harm, hp, q, hq, eq⟩ := asArm_valid rt ws hv hs ht
      obtain ⟨us, hus, hnw⟩ := accs_of_rawWords hp.1
      exact ⟨j, p, arm, us, ha, harm, hus, hnw, q, hq, eq⟩
  | false =>
      obtain ⟨us0, h0⟩ : ∃ us0, accs rt = some us0 := by
        cases h : accs rt with
        | none => simp [wc, h] at hw
        | some us0 => exact ⟨us0, rfl⟩
      obtain ⟨a, us, ha, hu, hn⟩ := accs_spine rt ws hsh hv us0 h0
      refine ⟨0, ws, a, us, by simp [asArm, hsh], by simp [ha], hu, by rw [hn, hs us0 h0], ws,
        by simp [ofArm, hsh], rfl⟩

theorem projM_nbB {g : G} {s : St} {t : Ty} {ws : List Word} (hb : isBoxed t = false) :
    projM g s t ws = ol ((asArm t ws).map fun (j, p) => (s, j, p)) := by
  simp only [projM, hb]; rfl

theorem Lay_boxR {σs : List Ty} {t τ rt : Ty} {ws : List Word} {w : Word} (hl : Lay σs t rt ws)
    (hS : (Ty.sum (close σs τ) rt).tier = .boxed) :
    Lay σs (.sum τ t) (.sum (close σs τ) rt) [w] := by
  obtain ⟨-, hsk, -, -, hly⟩ := hl
  refine ⟨fun us hu => by
      have hw := wc_boxed hS; simp only [wc, hu, Option.map_some, Option.some.injEq] at hw; simp [hw], ?_, wc_sum_ne _ _, Or.inl hS,
    by simp only [close, substTs, lyt, etok] at hly ⊢; rw [hly]⟩
  show Ty.sum (etok (skel (close σs τ))) (etok (skel rt)) = _
  rw [hsk]; rfl

/-- (T3c-5d) A boxed sum's left summand, itself boxed: read through the same reference. -/
theorem VR_boxLB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    (hS : (Ty.sum Ra Rb).tier = .boxed) (hRa : isBoxed Ra = true)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : B.tag < (armsOf Ra).length) (hv : VR ρ η a (vsh 0 (shp Ra)) [w])
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    VR ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun _ => ⟨fun _ => ?_, fun h => ?_⟩, fun h => ?_⟩⟩
  · rw [shp_lnorm]; exact hv
  · rw [isBoxed_lnorm, hRa] at h; cases h
  · rw [armsOf_lnorm, List.length_map] at h; omega

/-- (T3c-5d) A boxed sum's right summand, itself boxed. -/
theorem VR_boxRB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    (hS : (Ty.sum Ra Rb).tier = .boxed) (hRb : isBoxed Rb = true)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : (armsOf Ra).length ≤ B.tag) (hv : VR ρ η b (vsh (armsOf Ra).length (shp Rb)) [w])
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    VR ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun h => ?_, fun _ => ⟨fun _ => ?_, fun h => ?_⟩⟩⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega
  · rw [shp_lnorm, armsOf_lnorm, List.length_map, Nat.zero_add]; exact hv
  · rw [isBoxed_lnorm, hRb] at h; cases h

/-- (T3c-5d) A boxed type is one reference word. -/
theorem wc_isBoxed : ∀ t : Ty, isBoxed t = true → wc t = some 1 := by
  intro t
  induction t with
  | sum a b _ _ =>
      intro h; simp only [isBoxed, sumHead, Bool.true_and, beq_iff_eq] at h; exact wc_boxed h
  | refine t ψ ih =>
      intro h; simp only [isBoxed, sumHead, tier_refine] at h
      have := ih (by simpa [isBoxed] using h); simpa [wc, accs] using this
  | mu t ih =>
      intro h; simp only [isBoxed, sumHead, tier_mu] at h
      have := ih (by simpa [isBoxed] using h); simpa [wc, accs] using this
  | iall t ih =>
      intro h; simp only [isBoxed, sumHead, tier_iall] at h
      have := ih (by simpa [isBoxed] using h); simpa [wc, accs] using this
  | iex t ih =>
      intro h; simp only [isBoxed, sumHead, tier_iex] at h
      rw [wc_iex]; exact ih (by simpa [isBoxed] using h)
  | tex κ t ih =>
      intro h; simp only [isBoxed, sumHead, tier_tex] at h
      rw [wc_tex]; exact ih (by simpa [isBoxed] using h)
  | _ => intro h; simp [isBoxed, sumHead] at h

/-- (T3c-5d) Any words are valid at a boxed type (`Valid` does not look through
the reference). -/
theorem Valid_boxed : ∀ (t : Ty) (ws : List Word), isBoxed t = true → Valid t ws := by
  intro t
  induction t with
  | sum a b _ _ =>
      intro ws h; simp only [isBoxed, sumHead, Bool.true_and, beq_iff_eq] at h; exact Or.inl h
  | refine t ψ ih =>
      intro ws h; simp only [isBoxed, sumHead, tier_refine] at h
      simp only [Valid]; exact ih ws (by simpa [isBoxed] using h)
  | mu t ih =>
      intro ws h; simp only [isBoxed, sumHead, tier_mu] at h
      simp only [Valid]; exact ih ws (by simpa [isBoxed] using h)
  | iall t ih =>
      intro ws h; simp only [isBoxed, sumHead, tier_iall] at h
      simp only [Valid]; exact ih ws (by simpa [isBoxed] using h)
  | iex t ih =>
      intro ws h; simp only [isBoxed, sumHead, tier_iex] at h
      simp only [Valid]; exact ih ws (by simpa [isBoxed] using h)
  | tex κ t ih =>
      intro ws h; simp only [isBoxed, sumHead, tier_tex] at h
      simp only [Valid]; exact ih ws (by simpa [isBoxed] using h)
  | _ => intro ws h; simp [isBoxed, sumHead] at h

theorem lnorm_sig (t : Ty) : lnorm (sig t) = lnorm t := by
  simp only [sig, lnorm_er, lnorm_skel]

/-- (T3c-5d, β1) **An unboxed summand of a box, read back**: the box clause's
payload, loaded with grown views, rebuilds at the runtime summand into a value
there, valid (`Valid_of_VR`) and realising the static summand. -/
theorem case_arm_nb {ρ : Nat → Nat} {η : TEnv} {u ra : Ty} {j : Nat} {pay p1 q : List Word}
    (hc : Coh η) (hra : isBoxed ra = false) (hsg : sig ra = sig (cl ρ η.wit 0 0 u))
    (hq : ofArm (lnorm ra) j pay = some q) (hs : ShapeC (lnorm ra) q) (hw : wc (lnorm ra) ≠ none)
    (hvd : Valid (lnorm ra) q) (hvr : VR ρ η.unsee u (shp (lnorm ra)) q) (hp : WLe pay p1) :
    ∃ q1, ofArm ra j p1 = some q1 ∧ ShapeC ra q1 ∧ wc ra ≠ none ∧ Valid ra q1 ∧ VR ρ η u (shp ra) q1 := by
  obtain ⟨q1, hq1, hw1⟩ := ofArm_wle hp hq
  have e := hw1.vals
  have hs1 : ShapeC ra q1 := ShapeC_wc (wc_lnorm ra) (ShapeC_vals e hs)
  have hwc : wc ra ≠ none := by rw [← wc_lnorm]; exact hw
  have hvd1 : Valid (lnorm ra) q1 := Valid_vals _ _ _ e hvd
  have hvr1 : VR ρ η.unsee u (shp ra) q1 := by rw [← shp_lnorm]; exact VR_up _ _ _ _ hw1 hvr
  have hlT : lnorm (cl ρ η.wit 0 0 u) = lnorm ra := by rw [← lnorm_sig (cl ρ η.wit 0 0 u), ← hsg, lnorm_sig]
  have hsT : shp (cl ρ η.wit 0 0 u) = shp ra := by rw [← shp_sig (cl ρ η.wit 0 0 u), ← hsg, shp_sig]
  have c1 := VR_close hc.unsee ρ u [] 0 ρ ρ (shp ra) q1 (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have hvT : VR ρ (CE η.unsee) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) q1 := by
    rw [hsT]; exact c1.1 hvr1
  have hV := Valid_of_VR _ (CE η.unsee) ρ q1 (fun _ _ _ h => h) (by rw [hlT]; exact hvd1) hvT
  have hVr : Valid ra q1 := Valid_of_sig hsg.symm hV
  refine ⟨q1, ofArm_back hq1 ?_, hs1, hwc, hVr, VR_seen hc hvr1⟩
  intro x w hx hk hp1 hnl
  subst hp1
  exact null_arm hVr hs1 hra hx hk hq1 hnl

#print axioms accs_of_rawWords
#print axioms Valid_lnorm
#print axioms get_back
#print axioms decodeArm_back
#print axioms encodeArm_back
#print axioms PayOK_back
#print axioms ptr_of_armK
#print axioms Valid_ptrspine
#print axioms rawWords_popt
#print axioms armK_popt
#print axioms null_arm
#print axioms ofArm_back
#print axioms isBoxed_false
#print axioms Valid_of_VR
#print axioms wc_isBoxed
#print axioms Valid_boxed
#print axioms lnorm_sig
#print axioms case_arm_nb
#print axioms isBoxed_lnorm
#print axioms wc_boxed
#print axioms tier_lsum
#print axioms armsWc_lnorm
#print axioms VR_boxL
#print axioms VR_boxR
#print axioms Lay_box
#print axioms sumSpine_er
#print axioms sumSpine_int
#print axioms sumSpine_sig
#print axioms sumSpine_of_sumHead
#print axioms sumSpine_of_isBoxed
#print axioms VR_boxE0
#print axioms headArms_shp
#print axioms VR_boxE
#print axioms rawWords_iex_inner
#print axioms rawWords_tex_inner
#print axioms accs_inner
#print axioms accs_spine
#print axioms asArm_box
#print axioms projM_nbB
#print axioms Lay_boxR
#print axioms VR_boxLB
#print axioms VR_boxRB
#print axioms VR_ren0
#print axioms VR_ren
#print axioms vsh_zero
#print axioms VR_seen
#print axioms VR_store
#print axioms bh_shp
#print axioms IniR_ren

end TermSound
#print axioms TermSound.coupledOK_cl0
#print axioms TermSound.admitsIn_share
#print axioms TermSound.WitSh_call
#print axioms TermSound.rgnFree_clK
#print axioms TermSound.WitR_call
#print axioms CoreLang.Ty.ownHead
#print axioms TermSound.TEnv.ownTop
#print axioms TermSound.TEnv.selIni
#print axioms TermSound.TEnv.selIni_le_ini
#print axioms TermSound.TEnv.ownTop_congr
#print axioms TermSound.TEnv.selIni_le
#print axioms TermSound.TEnv.selIni_eq
#print axioms TermSound.TEnv.ownTop_shiftI
#print axioms TermSound.TEnv.selIni_shiftI
#print axioms TermSound.TEnv.ownTop_instT
#print axioms TermSound.TEnv.selIni_instT
#print axioms TermSound.TEnv.ownTop_tyEq
#print axioms TermSound.TEnv.selIni_tyEq
#print axioms TermSound.TEnv.ownTop_of_Clo
#print axioms TermSound.TEnv.ownTop_shiftT_insR
#print axioms TermSound.TEnv.selIni_shiftT_insR
#print axioms TermSound.TEnv.ownTop_shiftTN
#print axioms TermSound.TEnv.ownTop_shiftIN
#print axioms TermSound.TEnv.ownHead_cl0
#print axioms TermSound.TEnv.ownTop_cl
#print axioms TermSound.TEnv.selIni_cl
#print axioms TermSound.TEnv.selIni_le_at
#print axioms TermSound.TEnv.ownTop_substTs
#print axioms TermSound.TEnv.selIni_substTs
#print axioms TermSound.pre_rini
#print axioms TermSound.subE_rini
#print axioms TermSound.CE_rini
#print axioms TermSound.Ext.rini
#print axioms TermSound.modeIni_le_ini
#print axioms TermSound.modeIni_le
#print axioms TermSound.modeIni_shift
#print axioms TermSound.modeIni_inst
#print axioms TermSound.modeIni_clM
#print axioms TermSound.modeIni_meq
#print axioms TermSound.TEnv.selIni_loc
#print axioms TermSound.TEnv.insR_rini
#print axioms TermSound.RInv
#print axioms TermSound.RInv_unsee
#print axioms TermSound.RInv_push0
#print axioms TermSound.RInv_CE
#print axioms TermSound.VR_VRR
#print axioms TermSound.RInv_of
#print axioms TermSound.RetOKR_RetOK
#print axioms TermSound.FInvR_FInv
#print axioms TermSound.ResumeR_Resume
#print axioms TermSound.ThInvRE.thInvE
#print axioms TermSound.find_self_nodup
#print axioms TermSound.firstOK_nodup
