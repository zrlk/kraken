import WeakCore.TermPromClos

/-! # TermPromAlloc: `PromAllocF` ((C))

`TermPromClos.PromAllocF` (value and location halves), from the taken
step's certificate (stage A at the post-state from `TOut`, `TermNoHold.InvAtXF_of`; never `SysInvN`
along a certificate).
- `locPubV_VR` / `wordOK_locPubV`: `locPub_VR` / `wordOK_locPub` with the frontier bounded by the
  word's view (`ModeOK .pub` under `unsee`).
-/

namespace TermPromAlloc
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermMain TermInterf TermPlantF TermTyped TermPromClos
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The labels a pub/box-closed value names, with the frontier below the naming word's view. -/
def LPGoodV (η : TEnv) (l : AllocLabel) (v : Ts) : Prop :=
  (∃ c f, η.sto l = some c ∧ η.pfr l = some f ∧ (η.seen l ∨ f ≤ v)) ∨ ∃ B, η.box l = some B

/-- `decodeArm` keeps every `loc` word of its input with its view (unless the payload is empty). -/
theorem decodeArm_locV {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (h : decodeArm tr as ws = some (j, p)) :
    ∀ w ∈ ws, ∀ y g, w.val = .loc y g → (∃ w' ∈ p, ∃ g', w'.val = .loc y g' ∧ w'.view = w.view) ∨ p = [] := by
  intro w hw y g hv
  unfold decodeArm at h
  split at h
  · rename_i w0
    simp only [List.mem_singleton] at hw
    subst hw
    rw [hv] at h
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact .inl ⟨_, List.mem_singleton_self _, 0, rfl, rfl⟩
  · rename_i t w1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    split at h
    · rename_i j0 hj0
      rcases hw with rfl | rfl
      · rw [hv] at hj0; cases hj0
      · simp only [bind, Option.bind] at h
        split at h
        · cases h
        · dsimp only at h
          split at h
          · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
            exact .inr h.2.symm
          · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact .inl ⟨w, List.mem_singleton_self _, g, hv, rfl⟩
    · cases h
  · cases h

/-- `encodeArm` keeps every `loc` word of its payload with its view. -/
theorem encodeArm_locV {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) :
    ∀ w ∈ p, ∀ y g, w.val = .loc y g → ∃ w' ∈ q, ∃ g', w'.val = .loc y g' ∧ w'.view = w.view := by
  intro w hw y g hv
  rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
  · simp at hw
  · simp at hw; subst hw
    cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm =>
        cases hk : armK arm <;> simp [harm, hk, hv] at h
        all_goals (subst h; exact ⟨_, List.mem_singleton_self _, _, rfl, rfl⟩)
    | wide => simp [encodeArm] at h; subst h; exact ⟨w, by simp, g, hv, rfl⟩
    | boxed => simp [encodeArm] at h
  · cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm => cases armK arm <;> simp [harm] at h
    | wide => simp [encodeArm] at h
    | boxed => simp [encodeArm] at h

/-- `ofArm` keeps every `loc` word of its payload with its view. -/
theorem ofArm_locV {t : Ty} {j : Nat} {p q : List Word} (h : ofArm t j p = some q) :
    ∀ w ∈ p, ∀ y g, w.val = .loc y g → ∃ w' ∈ q, ∃ g', w'.val = .loc y g' ∧ w'.view = w.view := by
  unfold ofArm at h
  split at h
  · exact encodeArm_locV h
  · split at h
    · simp at h; subst h; intro w hw y g hv; exact ⟨w, hw, g, hv, rfl⟩
    · contradiction

/-- **Inversion, with views.**  Every `loc` word of an `own`- and region-free value names a box or
a published cell whose frontier is below the word's view (or seen). -/
theorem locPubV_VR : ∀ (T : Ty) (ke : KEnv) (ρ : Nat → Nat) (η : TEnv) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → Ty.noOwnIn ke T = true → rgnFree T = true →
    wc T = some ws.length → Valid T ws → VR ρ η T (shp T) ws →
    ∀ w ∈ ws, ∀ x g, w.val = .loc x g → LPGoodV η x.label w.view := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    simp only [Ty.noOwnIn, rgnFree, Bool.and_eq_true] at hno hrf
    rw [wc_prod] at hlen
    cases ha : wc a with
    | none => simp [ha] at hlen
    | some na =>
      cases hb : wc b with
      | none => simp [ha, hb] at hlen
      | some nb =>
        simp [ha, hb] at hlen
        obtain ⟨ra, rb, hr, hv⟩ := hv
        simp only [shp, Shp.prod.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hle, hva, hvb⟩ := hv na (by rw [shp_wc]; exact ha)
        obtain ⟨Va, Vb⟩ := hval na ha
        rw [← List.take_append_drop na ws] at hw
        rcases List.mem_append.1 hw with h | h
        · exact iha ke ρ η _ hrel hno.1 hrf.1 (by rw [ha, List.length_take]; congr 1; omega) Va hva w h x g hx
        · exact ihb ke ρ η _ hrel hno.2 hrf.2 (by rw [hb, List.length_drop]; congr 1; omega) Vb hvb w h x g hx
  | sum a b iha ihb =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    simp only [Ty.noOwnIn, rgnFree, Bool.and_eq_true] at hno hrf
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have htl : (Ty.sum (lnorm a) (lnorm b)).tier = (Ty.sum a b).tier := tier_lnorm (.sum a b)
    rcases hcase with ⟨-, y, s, B, hvals, -, hbox, -⟩ | ⟨j, p, hd, hA, hB⟩
    · have hm := locPub_mem_val hvals hw
      rw [hx] at hm
      simp at hm
      obtain ⟨rfl, -⟩ := hm
      exact Or.inr ⟨B, hbox⟩
    · rcases hval with htb | ⟨j', p', arm, hd', -, -, ⟨q0, he, hveq⟩, hA', hB'⟩
      · rw [htl, htb] at hd; simp [decodeArm] at hd
      · have hd2 := decodeArm_mono (arms_lnorm (.sum a b)) hd'
        rw [htl] at hd
        have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
        simp only [Prod.mk.injEq] at hjp
        obtain ⟨rfl, rfl⟩ := hjp
        have hm : w.val ∈ q0.map (·.val) := hveq ▸ List.mem_map_of_mem hw
        obtain ⟨w0, hw0, hv0⟩ := List.mem_map.1 hm
        obtain ⟨w1', hw1', -, -⟩ := locPub_encFwd he w0 hw0 x g (hv0.trans hx)
        obtain ⟨w1, hw1, g1, hv1, hvw1⟩ : ∃ w1 ∈ p, ∃ g1, w1.val = .loc x g1 ∧ w1.view = w.view := by
          rcases decodeArm_locV hd w hw x g hx with h | h
          · exact h
          · rw [h] at hw1'; simp at hw1'
        have hlenA : (armsOf (lnorm a)).length = (armsOf a).length := by
          rw [armsOf_lnorm, List.length_map]
        by_cases hj : j < (armsOf a).length
        · obtain ⟨q, hq, hvq⟩ := hA (by rw [hlenA]; exact hj)
          obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
          have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
          subst hqq
          obtain ⟨w2, hw2, g2, hv2, hvw2⟩ := ofArm_locV hq' w1 hw1 x g1 hv1
          have hwc : wc a = some q'.length := by
            cases hu : accs a with
            | none => simp [wc, hu] at hwq
            | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
          rw [shp_lnorm] at hvq
          have hr := iha ke ρ η q' hrel hno.1 hrf.1 hwc hvalq hvq w2 hw2 x g2 hv2
          rw [hvw2, hvw1] at hr
          exact hr
        · have hj2 : (armsOf a).length ≤ j := Nat.le_of_not_lt hj
          obtain ⟨q, hq, hvq⟩ := hB (by rw [hlenA]; exact hj2)
          obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB' hj2
          rw [hlenA] at hq
          have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
          subst hqq
          obtain ⟨w2, hw2, g2, hv2, hvw2⟩ := ofArm_locV hq' w1 hw1 x g1 hv1
          have hwc : wc b = some q'.length := by
            cases hu : accs b with
            | none => simp [wc, hu] at hwq
            | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
          rw [shp_lnorm] at hvq
          have hr := ihb ke ρ η q' hrel hno.2 hrf.2 hwc hvalq hvq w2 hw2 x g2 hv2
          rw [hvw2, hvw1] at hr
          exact hr
  | refine t ψ ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih ke ρ η ws hrel hno hrf hlen hval hv.1
  | iall t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih ke (vcons 0 ρ) η ws hrel hno hrf hlen hval (hv 0)
  | iex t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    rw [wc_iex] at hlen
    exact ih ke (vcons w ρ) η ws hrel hno hrf hlen hval hv
  | mu t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih (none :: ke) ρ (η.push0 (cl ρ η.wit 0 0 (.mu t))) ws (locPub_push0_rels hrel _) hno hrf hlen hval hv
  | tex κ t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    simp only [Ty.noOwnIn, Bool.and_eq_true] at hno
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    rw [wc_tex] at hlen
    exact ih (some κ :: ke) ρ (η.push0 s) ws (locPub_push0_rels hrel s) hno.2 hrf hlen hval hv
  | tvar k =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    obtain ⟨ws', -, hg⟩ := hv
    exact absurd hg (hrel _ _ _)
  | ptr μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      obtain ⟨a, c, h1, -, h3, -, ⟨f, hf, hS⟩, -⟩ := hv
      have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact Or.inl ⟨c, f, h3, hf, hS.imp id (fun h => h w hw)⟩
  | ptrOpt μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      rcases hv with h0 | ⟨a, c, h1, -, h3, -, ⟨f, hf, hS⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact Or.inl ⟨c, f, h3, hf, hS.imp id (fun h => h w hw)⟩
  | loc μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      rcases hv with ⟨h0, -⟩ | ⟨a, c, U, h1, h3, -, -, ⟨f, hf, hS⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact Or.inl ⟨c, f, h3, hf, hS.imp id (fun h => h w hw)⟩
  | void =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    simp [VR] at hv
  | intS i =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    have hm := locPub_mem_val hv hw
    rw [hx] at hm; simp at hm
  | opq _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | int =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | tid =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, c, hn, hs, -, hmo⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm
    simp only [List.mem_singleton, Val.loc.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    obtain ⟨f, hf, hS⟩ := hmo
    exact Or.inl ⟨c, f, hs, hf, hS.imp id (fun h => h w hw)⟩
  | fix sg wd =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | lanes sg wd =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | code a b _ _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨i, d, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | word r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases hg : P.ghost with
    | true =>
      simp [wc, accs, hg, nWords] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw
    | false =>
      obtain ⟨n, hn, -⟩ := hv.2 hg
      have hm := locPub_mem_val hn hw
      rw [hx] at hm; simp at hm
  | word2 r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | epair r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | array i t _ =>
    intro ke ρ η ws hrel hno hrf hlen
    simp [wc, accs] at hlen
  | unit | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw
    simp [wc, accs, nWords] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw

/-- **`wordOK_locPub` with views**: a `loc` word of a `noOwnIn`/`rgnFree` cell's `WordOK` value names a
box or a cell whose frontier is at most the word's view. -/
theorem wordOK_locPubV {E : TEnv} {T : Ty} {o : Nat} {w : Word} {a : Address} {g : Nat}
    (h : WordOK E T o w) (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true)
    (hv : w.val = .loc a g) :
    (∃ c f, E.sto a.label = some c ∧ E.pfr a.label = some f ∧ f ≤ w.view) ∨ ∃ B, E.box a.label = some B := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hval⟩, hsh⟩, hget, hle, -⟩ := h
  have hS : Ty.noOwnIn [] S = true ∧ rgnFree S = true ∧ accs S ≠ none := by
    rcases hseg with ⟨-, rfl, hacc⟩ | ⟨N, us, j, rfl, hus, -, -⟩
    · exact ⟨hno, hrf, hacc⟩
    · simp only [Ty.noOwnIn, rgnFree] at hno hrf
      exact ⟨hno, hrf, by rw [hus]; simp⟩
  obtain ⟨hnoS, hrfS, hacc⟩ := hS
  have hwc : wc S = some ws.length := by
    cases hu : accs S with
    | none => exact absurd hu hacc
    | some us => simp only [wc, hu, Option.map_some]; rw [hsh us hu]
  have hrel : ∀ k r vs, ¬ (CE E.unsee).rels k r vs := fun _ _ _ h => h
  have hw0 : w0.val = .loc a g := hle.1.trans hv
  rcases locPubV_VR S [] (fun _ => 0) (CE E.unsee) ws hrel hnoS hrfS hwc hval hvr w0
    (List.mem_of_getElem? hget) a g hw0 with ⟨c, f, hc, hf, hs⟩ | ⟨B, hB⟩
  · refine .inl ⟨c, f, hc, hf, ?_⟩
    rcases hs with hs | hs
    · exact hs.elim
    · exact Nat.le_trans hs (hle.2 a g hw0)
  · exact .inr ⟨B, hB⟩

/-- A one-word slot of a unit at offset `o` of a laid-out type lies inside its layout. -/
theorem oneAt_lt_acc {T U : Ty} {o j : Nat} {L us : List Acc} (h : AtOff T o U) (hL : accs T = some L)
    (hU : accs U = some us) (hj : TermFul.OneAt us j) : o + j < nWords L := by
  have h1 := AtOff_bound h hL hU
  have h2 := TermFul.OneAt_lt hj
  omega

/-- A one-word slot of a unit at offset `o` of an array of literal length lies inside the array. -/
theorem oneAt_lt_arr {N : Nat} {e U : Ty} {o j : Nat} {L us : List Acc} (h : AtOff (.array (.lit N) e) o U)
    (hL : accs e = some L) (hU : accs U = some us) (hj : TermFul.OneAt us j) : o + j < N * nWords L := by
  rcases AtOff_arr_elem h rfl with hT | ⟨us', jj, o', hus', hjj, ho, h'⟩
  · rw [hT] at hU; simp [accs] at hU
  · rw [hL] at hus'
    cases hus'
    have h1 := oneAt_lt_acc h' hL hU hj
    have h2 : (jj + 1) * nWords L ≤ N * nWords L := Nat.mul_le_mul_right _ hjj
    rw [Nat.succ_mul] at h2
    omega

/-- A one-word slot of a unit of a cell's type is inside every `CellOK` value list of it. -/
theorem oneAt_lt_cellOK {E : TEnv} {n : Nat} {T U : Ty} {vals : List Word} {o j : Nat} {us : List Acc}
    (hc : CellOK E n T vals) (h : AtOff T o U) (hU : accs U = some us) (hj : TermFul.OneAt us j) :
    o + j < vals.length := by
  rcases hc with ⟨hw, -⟩ | ⟨N, e, L, hT, hL, -, hl, -⟩
  · cases hT : accs T with
    | none => simp [wc, hT] at hw
    | some L =>
      simp only [wc, hT, Option.map_some, Option.some.injEq] at hw
      rw [← hw]
      exact oneAt_lt_acc h hT hU hj
  · subst hT
    rw [hl]
    exact oneAt_lt_arr h hL hU hj

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The value half of `PromAllocF`**: an outstanding promise of the stepper, at a `noOwnIn`/
`rgnFree` cell of `E'`, names no cell of `E'` at a label the step allocates.  Its certificate from
`c'` (stage A at `E'`, `TOut`) fulfils it with a `WordOK` word (`certified_promWordX`): the named
cell gets a frontier `f` at most the promise's view (`wordOK_locPubV`; a box label holds no cell,
`BoxInv`).  The label has no frontier in `E'`, so `f` is at least the post-step `vWr` (`FrBound`),
which is at least the pre-step memory size less one (`WrUp`, the step allocates); but the promise is
an old message whose view is below its timestamp (`PromViewLt`). -/
theorem promAlloc_val (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    (hn0 : TermPlantF.PromViewLtR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {L : AllocLabel} (hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc L) {t : Ts} {m : Msg}
    (ht : t ∈ r.2.2.promises) (hm : c'.mem[t]? = some m) {a' : Address} {g : Nat} (hv : m.val = .loc a' g)
    {cm : Cell} (hcm : E'.sto m.loc.label = some cm) (hno : Ty.noOwnIn [] cm.ty = true)
    (hrf : rgnFree cm.ty = true) {cl : Cell} (hcl : E'.sto a'.label = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : a'.label ≠ L := by
  intro hL
  subst hL
  have hgf := gfoot_of X Y Z
  have hfr0 := X.inv.gfresh X.hth r.2.2.nalloc a'.label hF
  have hpfr : E'.pfr a'.label = none := by
    rcases hgf.2.2.2.2.1 a'.label with e | ⟨-, -, -, -, cq, hcq, -⟩ | ⟨-, -, e⟩
    · exact e.trans hfr0.2.2
    · rw [hfr0.1] at hcq; cases hcq
    · rw [post_sto_fresh hF, hcl] at e; cases e
  have ht0 : t ∈ th.promises := tctx_sub X t ht
  have hlt : t < c.mem.size := X.inv.plt i th t X.hth ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  obtain ⟨m1, hm1, hvl⟩ := TermPlantF.promViewLt_run hn0 X.run i th t X.hth ht0
  rw [hm0] at hm1
  cases hm1
  have hwu := tstep_wrUp _ _ _ _ r X.hr
  obtain ⟨n1, hn1, hn2, -⟩ := hF
  have hsz : c.mem.size ≤ r.2.2.vs.vWr + 1 := hwu.2.2.2 (by show th.nalloc < r.2.2.nalloc; omega)
  have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 Z hS hPfr (hrun X S hS).1
  obtain ⟨hFt, hRE, hm', -⟩ := id Z
  have hg := TermTyped.gOf_thread X.hc'
  have hSC0 : StoClo (CE η) := by
    rw [Y.1]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hbo : (gOf p k arch c' i).boxFence = true := by rw [hg]; exact X.inv.bf
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  have hx0 := TermNoHold.InvAtXF_ofA (hTy := (TermNoHold.TCtxX.tyPost X Y.1 hFt (TermMain.TOutC.newTy Z)).1) (hRc := (TermNoHold.TCtxX.tyPost X Y.1 hFt (TermMain.TOutC.newTy Z)).2) (p := p) (k := k) (arch := arch) (Ea := Cut Eg i S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hm')
    (StoClo_EFoot hFt hSC0) hbo (by rw [hst]; exact hAP.1) (.inr hAP.2)
  obtain ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, -, -, -, hIH0, hTyP, hRcP⟩ := hx0
  have hX : InvAtX p k arch i E' _ _ c' (Ea := Cut Eg i S) := ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, fun _ _ _ h => h.elim, hIH0, hTyP, hRcP⟩
  have hsc := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).2
  have htp : t ∈ TermFul.promsOf c' i := by rw [TermFul.promsOf_some X.e3]; exact ht
  obtain ⟨c2, th2, E2, -, -, -, hx2, -, hm2, hok, hfb2⟩ := certified_promWordX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert htp hm
  rcases hok cm hcm with hu | hw
  · rw [hv] at hu; cases hu
  rcases wordOK_locPubV hw hno hrf hv with ⟨c3, f, hs3, hf3, hle⟩ | ⟨B, hB⟩
  · have hvw : r.2.2.vs.vWr ≤ f := hfb2.1 a'.label c3 f hpfr hs3 hf3
    have hle2 : f ≤ m.view := hle
    have h5 : c.mem.size ≤ t :=
      Nat.le_trans hsz (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans hvw hle2) hvl))
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h5 hlt)
  · have h4 := (hm2.2.2.2.2.2.2.2.2.2.1.2.2 _ B hB).1
    rw [hx2.2.2.2.2.1 _ _ hcl] at h4
    cases h4

/-- **The location half of `PromAllocF`**: an outstanding promise of the stepper does not lie at
a label the step allocates.  The promise is at a cell of `E'` (`certified_promLoc`; a label of the
step is below the new allocation count), a fresh cell of the stepper without a frontier (`EFoot`),
in a one-word slot of it (`SWOne` at its certificate's fulfilling write).  The allocation wrote a
message there past the old memory (`NewAtT`), so not a promise; the owner's invariant at `E'`
(`LatestSF`, no frontier) puts coherence at or past it, past the promise (an old message), against
`certified_promAbove`. -/
theorem promAlloc_loc (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {L : AllocLabel} (hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc L) {t : Ts} {m : Msg}
    (ht : t ∈ r.2.2.promises) (hm : c'.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : m.loc.label ≠ L := by
  intro hL
  have hgf := gfoot_of X Y Z
  have hfr0 := X.inv.gfresh X.hth r.2.2.nalloc L hF
  have ht0 : t ∈ th.promises := tctx_sub X t ht
  have hlt : t < c.mem.size := X.inv.plt i th t X.hth ht0
  have hpa : r.2.2.vs.coh m.loc < t := TermCert.certified_promAbove X.cert X.e3 ht hm
  have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 Z hS hPfr (hrun X S hS).1
  obtain ⟨hFt, hRE, hm', -⟩ := id Z
  have hg := TermTyped.gOf_thread X.hc'
  have hSC0 : StoClo (CE η) := by
    rw [Y.1]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hbo : (gOf p k arch c' i).boxFence = true := by rw [hg]; exact X.inv.bf
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  have hx0 := TermNoHold.InvAtXF_ofA (hTy := (TermNoHold.TCtxX.tyPost X Y.1 hFt (TermMain.TOutC.newTy Z)).1) (hRc := (TermNoHold.TCtxX.tyPost X Y.1 hFt (TermMain.TOutC.newTy Z)).2) (p := p) (k := k) (arch := arch) (Ea := Cut Eg i S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hm')
    (StoClo_EFoot hFt hSC0) hbo (by rw [hst]; exact hAP.1) (.inr hAP.2)
  have hsc := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => ((hrun X S hS).2 c1 h1 h2).2
  have htp : t ∈ TermFul.promsOf c' i := by rw [TermFul.promsOf_some X.e3]; exact ht
  have hloc := TermNoHold.certified_promLoc (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hx0 (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert htp hm
  rw [hL] at hloc
  have hsL : ∃ cl, E'.sto L = some cl := by
    rcases hloc with ⟨cl, hcl⟩ | ⟨jj, hjj, hlj⟩
    · exact ⟨cl, hcl⟩
    · exfalso
      obtain ⟨j0, -, hj0, hl0⟩ := hF
      have hi : i < c.ths.size := TermCert.arr_lt X.hth
      have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
      have hlb : c'.lbase = c.lbase := (threadSteps_lbase X.hc').1
      rw [TermStep.threadSteps_n X.hc', hlb] at hlj
      have e := freshLabel_inj (base := c.lbase) (Cfg.lt_n hi) (Cfg.lt_n hi) (hlj.symm.trans hl0)
      omega
  obtain ⟨cl, hsl⟩ := hsL
  have hCE : (CE η).sto L = none := by
    rw [Y.1]
    show cutSto Eg i L = none
    cases e : cutSto Eg i L with
    | none => rfl
    | some c5 =>
      have h5 := cutSto_sub e
      rw [hfr0.1] at h5; cases h5
  rcases hFt.2.2.1 L with e | ⟨-, T, hT, -, -, hN⟩
  · rw [e, hCE] at hsl; cases hsl
  have hpfr : E'.pfr L = none := by
    rcases hgf.2.2.2.2.1 L with e | ⟨-, -, -, -, cq, hcq, -⟩ | ⟨-, -, e⟩
    · exact e.trans hfr0.2.2
    · rw [hfr0.1] at hcq; cases hcq
    · rw [post_sto_fresh hF, hT] at e; cases e
  have hX : InvAtX p k arch i E' c'.mem.size r.2.2.vs.vWr c' (Ea := Cut Eg i S) := by
    obtain ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, -, -, -, hIH0, hTyP, hRcP⟩ := hx0
    exact ⟨thx, E, hthx, hx, hTEx, hmx, hSCx, hbox, hfb, hfr, fun _ _ _ h => h.elim, hIH0, hTyP, hRcP⟩
  obtain ⟨c1, c2, th1, th2, ρ1, η1, cx1, E2, -, -, -, -, -, -, hx1, hE, hTy, htv, hi, hmi, hscope, hpa1, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert htp hm
  obtain ⟨cl1, o1, U, us, j1, hcl1, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ1 η1 cx1 _ _ hE hTy htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa1 hsw
  rw [hx1.2.2.2.2.1 _ _ (by rw [hL]; exact hT)] at hcl1
  cases hcl1
  have hun : NewU c.mem.size r.1 ⟨L, m.loc.offset⟩ := by
    rcases hN.1 with ⟨Lw, hLw, hall⟩ | ⟨K, e, Lw, hTe, hLw, hall⟩
    · exact hall _ (by rw [ho]; exact oneAt_lt_acc h1o hLw hus hj)
    · have h1o' : AtOff (.array (.lit K) e) o1 U := by rw [← hTe]; exact h1o
      exact hall _ (by rw [ho]; exact oneAt_lt_arr h1o' hLw hus hj)
  obtain ⟨tu, mu, htu, hmu, hmul⟩ := hun
  have hnp : tu ∉ r.2.2.promises := fun h5 =>
    Nat.lt_irrefl _ (Nat.lt_of_le_of_lt htu (X.inv.plt i th tu X.hth (tctx_sub X tu h5)))
  have hown : (⟨T, some (CE η).tid⟩ : Cell).owner = some E'.tid := by rw [hFt.2.1]
  obtain ⟨vals, hcv, hlat, -⟩ := hm'.2.1 L _ hT hown
  have hol := oneAt_lt_cellOK hcv h1o hus hj
  obtain ⟨-, -, hlater⟩ := hlat (o1 + j1) _ (List.getElem?_eq_getElem hol)
  have hcoh : tu ≤ r.2.2.vs.coh ⟨L, o1 + j1⟩ := Nat.le_of_not_lt fun h5 => by
    rcases hlater tu mu h5 hmu (by rw [hmul, ho]) with h6 | ⟨h6, -⟩
    · exact hnp h6
    · exact h6 hpfr
  have hmloc : m.loc = ⟨L, o1 + j1⟩ := by rw [← hL, ← ho]
  rw [hmloc] at hpa
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans htu hcoh) (Nat.lt_trans hpa hlt))

/-- **`PromAllocF`**: the value half (`promAlloc_val`) and the location half (`promAlloc_loc`). -/
theorem promAllocF_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : TermPlantF.CertRunT p k arch Sp Init MintOK c0)
    (hn0 : TermPlantF.PromViewLtR p k arch Sp c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : PromAllocF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr L hF t m ht hm
  exact ⟨promAlloc_loc (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X Y Z hS hPfr hF ht hm,
    fun a' g hv cm hcm hno hrf cl hcl => promAlloc_val (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hn0 X Y Z hS hPfr hF ht hm hv hcm hno hrf hcl⟩

end

end TermPromAlloc

#print axioms TermPromAlloc.decodeArm_locV
#print axioms TermPromAlloc.encodeArm_locV
#print axioms TermPromAlloc.ofArm_locV
#print axioms TermPromAlloc.locPubV_VR
#print axioms TermPromAlloc.wordOK_locPubV
#print axioms TermPromAlloc.oneAt_lt_acc
#print axioms TermPromAlloc.oneAt_lt_arr
#print axioms TermPromAlloc.oneAt_lt_cellOK
#print axioms TermPromAlloc.promAlloc_val
#print axioms TermPromAlloc.promAlloc_loc
#print axioms TermPromAlloc.promAllocF_of
