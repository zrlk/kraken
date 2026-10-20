import WeakCore.TermK2aBox
import WeakCore.TermK2aSum
import WeakCore.TermK2aLoad
import WeakCore.TermK2aLabsV

/-!
# K-2a: `case` on a boxed scrutinee, with box loads (K1c)

`sum_caseTX`: `case`, every tier, meets `StepOKX` with no box-load premise.  The non-boxed summand
of a boxed scrutinee is rebuilt from words loaded at the box's payload slots (`projM_pos`); each of
its counted words naming `a` is a box payload word naming `a` whose view reaches `a`'s frontier
(`labsV_cnt`), at a slot whose message index is the loaded word's `rts` (`BoxLW`).
-/

namespace TermK2aCaseB

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermK2a TermK2aLd
open TermK2aBox TermK2aSum
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem offs_zero {x : Address} (hx : x.offset = 0) (k : Nat) : offs x k = ⟨x.label, k⟩ := by
  cases x; simp only [offs] at hx ⊢; rw [hx, Nat.zero_add]

/-- **Positions of a box projection**: payload word `o` was read from a message at the box's slot
`o + 1`, carrying its value, at index `≤` its `rts`. -/
theorem projM_pos {g : G} {s : St} {t : Ty} {pw : Word} {x : Address} (hb : isBoxed t = true)
    (hpw : pw.val = .loc x 0) (hx : x.offset = 0) {r : St × Nat × List Word} (hr : r ∈ projM g s t [pw]) :
    ∀ o w1, r.2.2[o]? = some w1 → ∃ (u : Nat) (m : Msg), s.mem[u]? = some m ∧ m.loc = ⟨x.label, o + 1⟩ ∧
      m.val = w1.val ∧ u ≤ w1.rts := by
  have hsplit : projM g s t [pw] = (loadUnits g.arch pw x false [.one] 0 s).flatMap fun (s1, tw) =>
      match tw with
      | [tag] =>
          match tag.val with
          | .num j =>
              match (armsOf t)[j]?.bind accs with
              | some us => (loadUnits g.arch pw x false us 1 s1).map fun (s2, p) => (s2, j, p)
              | none => []
          | _ => []
      | _ => [] := by
    simp only [projM, hb, ite_true, addrOf, hpw]; rfl
  rw [hsplit] at hr
  obtain ⟨⟨s1, tw⟩, hr1, hr⟩ := List.mem_flatMap.1 hr
  have hin : ∃ (j : Nat) (usP : List Acc) (s2 : St) (p : List Word),
      (s2, p) ∈ loadUnits g.arch pw x false usP 1 s1 ∧ r = (s2, j, p) := by
    simp only at hr
    split at hr
    · split at hr
      · split at hr
        · obtain ⟨⟨s2, p⟩, h2, he⟩ := List.mem_map.1 hr; exact ⟨_, _, s2, p, h2, he.symm⟩
        · cases hr
      · cases hr
    · cases hr
  obtain ⟨_, usP, s2, p, h2, rfl⟩ := hin
  have e1 : s1.mem = s.mem := (loadUnits_frame _ _ _ _ hr1).1
  have hR := TermK2aLoad.loadUnits_readsR usP 1 s1 _ h2 [] (fun _ _ h => by cases h)
  have hlen := TermK2aLoad.readsR_len usP 1 p hR
  intro o w1 ho
  simp only at ho ⊢
  have hol : o < nWords usP := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 ho).1
  obtain ⟨u, d, hu⟩ := TermCntLoc.unitAt_some usP o hol
  have hbd := TermCntLoc.unitAt_bound usP o hu
  have hat := TermK2aLoad.readsR_at usP 1 p hR o u d hu
  rw [e1] at hat
  cases u with
  | one =>
    have hd := TermK2aLoad.unitAt_one hu
    subst hd
    rw [Nat.sub_zero, show Acc.size .one = 1 from rfl, TermCntLoc.take_drop_one ho] at hat
    obtain ⟨t0, m, hm, hl, hv, hr0, -⟩ := hat
    refine ⟨t0, m, hm, ?_, hv.symm, by rw [← hr0]; exact Nat.le_refl _⟩
    rw [hl, offs_zero hx, Nat.add_comm]
  | two =>
    simp only [Acc.size] at hbd
    have hd : d = 0 ∨ d = 1 := by omega
    rcases hd with rfl | rfl
    · obtain ⟨y, hy⟩ : ∃ y, p[o + 1]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlen]; omega)⟩
      rw [Nat.sub_zero, show Acc.size .two = 2 from rfl, TermCntLoc.take_drop_two ho hy] at hat
      obtain ⟨t0, -, m0, -, hm0, -, hl0, -, -, hv0, hr0, -⟩ := hat
      refine ⟨t0, m0, hm0, ?_, hv0.symm, by rw [← hr0]; exact Nat.le_refl _⟩
      rw [hl0, offs_zero hx, Nat.add_comm]
    · obtain ⟨o1, rfl⟩ : ∃ o1, o = o1 + 1 := ⟨o - 1, (Nat.sub_add_cancel hbd.1).symm⟩
      have hb2 : o1 + 2 ≤ nWords usP := by have := hbd.2.2; simp only [Nat.add_sub_cancel] at this; exact this
      obtain ⟨y, hy⟩ : ∃ y, p[o1]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlen]; omega)⟩
      rw [Nat.add_sub_cancel, show Acc.size .two = 2 from rfl, TermCntLoc.take_drop_two hy ho] at hat
      obtain ⟨-, t1, -, m1, -, hm1, -, hl1, -, -, -, hv1, hr1, -⟩ := hat
      refine ⟨t1, m1, hm1, ?_, hv1.symm, by rw [← hr1]; exact Nat.le_refl _⟩
      rw [hl1, offs_zero hx, Nat.add_comm 1 o1]

/-- The payload position `ofArm t` places at value position `i`. -/
def oi (t : Ty) (i : Nat) : Nat := if sumHead t = true ∧ t.tier = .wide then i - 1 else i

/-- **`ofArm` by position**: a `loc` word of the built value is the payload word at `oi t i`, with
its view and `rts`, naming the same label. -/
theorem ofArm_pos {t : Ty} {j : Nat} {p q : List Word} (h : ofArm t j p = some q) {i : Nat} {w : Word}
    (hi : q[i]? = some w) {a : Address} {g : Nat} (hl : w.val = .loc a g) :
    ∃ w0, p[oi t i]? = some w0 ∧ w0.view = w.view ∧ w0.rts = w.rts ∧ ∃ gP, w0.val = .loc a gP := by
  unfold ofArm at h
  by_cases hs : sumHead t = true
  · simp only [hs, ↓reduceIte] at h
    cases htr : t.tier with
    | boxed => rw [htr] at h; simp [encodeArm] at h
    | wide =>
      have ho : oi t i = i - 1 := by simp [oi, hs, htr]
      rw [ho]
      rw [htr] at h
      rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
      · simp only [encodeArm, Option.some.injEq] at h
        subst h
        rcases i with _ | _ | i <;> simp at hi <;> subst hi <;> cases hl
      · simp only [encodeArm, Option.some.injEq] at h
        subst h
        rcases i with _ | _ | i <;> simp at hi
        · subst hi; cases hl
        · subst hi; exact ⟨_, rfl, rfl, rfl, g, hl⟩
      · simp [encodeArm] at h
    | niche =>
      have ho : oi t i = i := by simp [oi, htr]
      rw [ho]
      rw [htr] at h
      simp only [encodeArm, bind, Option.bind] at h
      cases h1 : (armsOf t)[j]? with
      | none => simp [h1] at h
      | some arm =>
        simp only [h1] at h
        rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
        · cases hk : armK arm <;> simp [hk] at h
          subst h
          rcases i with _ | i <;> simp at hi
          subst hi; cases hl
        · cases hk : armK arm <;> simp only [hk] at h
          all_goals first
            | (simp at h; done)
            | (cases hw : w0.val <;> simp only [hw] at h <;> (try split at h) <;> simp at h <;> subst h <;>
                rcases i with _ | i <;> simp at hi <;> subst hi <;> simp [cst, Promises.TVal.mk0] at hl
                <;> skip)
          all_goals (obtain ⟨rfl, -⟩ := hl; exact ⟨w0, rfl, rfl, rfl, _, hw⟩)
        · cases hk : armK arm <;> simp [hk] at h
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    have ho : oi t i = i := by simp [oi, hs]
    rw [ho]
    split at h
    · cases h; exact ⟨w, hi, rfl, rfl, g, hl⟩
    · cases h

theorem getElem_val {a b : List Word} (e : VEq a b) {o : Nat} {x y : Word} (ha : a[o]? = some x)
    (hb : b[o]? = some y) : x.val = y.val := by
  have h := congrArg (fun l => l[o]?) e
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at h
  exact h

theorem getElem_veq {a b : List Word} (e : VEq a b) {o : Nat} {x : Word} (ha : a[o]? = some x) :
    ∃ y, b[o]? = some y := by
  have h := congrArg (fun l => l[o]?) e
  simp only [List.getElem?_map, ha, Option.map_some] at h
  cases hb : b[o]? with
  | none => rw [hb] at h; cases h
  | some y => exact ⟨y, rfl⟩

/-- **Box-load words** (the D2 box-load contract, discharged): the value rebuilt at a non-boxed
summand from words `p1` loaded at a box's payload slots names `a` only through a payload word
naming `a` whose view reaches `a`'s frontier (`a` not a box, `VR` read unseen), read from that
word's slot at an index `≤` the counted word's `rts`. -/
theorem boxLW_arm {ρ : Nat → Nat} {η : TEnv} {uu ty : Ty} {jP : Nat} {B0 : Box} {q p1 q1 : List Word}
    {x0 : Address} {mem : Memory} {ga : AllocLabel}
    (hc : Coh η) (hgb : η.box ga = none) (hsg : sig ty = sig (TermClose.cl ρ η.wit 0 0 uu))
    (hq : ofArm (lnorm ty) jP B0.pay = some q) (hsq : ShapeC (lnorm ty) q) (hwq : wc (lnorm ty) ≠ none)
    (hvd : Valid (lnorm ty) q) (hvr : VR ρ η.unsee uu (shp ty) q)
    (hWp : WLe B0.pay p1) (hq1 : ofArm ty jP p1 = some q1) (hB0 : η.box x0.label = some B0)
    (hpos : ∀ o w1, p1[o]? = some w1 → ∃ (u : Nat) (m : Msg), mem[u]? = some m ∧ m.loc = ⟨x0.label, o + 1⟩ ∧
      m.val = w1.val ∧ u ≤ w1.rts) :
    ∀ w ∈ pubWords ty q1, BoxLW (CE η) mem ga w := by
  intro w hw hn
  obtain ⟨i, w1, hi, hq1i, hn1, hr1⟩ := TermPubPos.pubWords_pos hw hn
  have hq1l := ofArm_lnorm hq1
  obtain ⟨qP, hqP, hvq⟩ := ofArm_vals hWp.vals hq
  rw [hq1l, Option.some.injEq] at hqP
  subst hqP
  have hiP : i ∈ cntIdx ty q := by
    rw [TermCntLoc.cntIdx_eq, TermCntLoc.cntK_of_veq ty 0 hvq, ← TermCntLoc.cntIdx_eq]; exact hi
  obtain ⟨w0q, hw0q⟩ := getElem_veq (show VEq q1 q from hvq.symm) hq1i
  have hval : w0q.val = w1.val := (getElem_val hvq.symm hq1i hw0q).symm
  obtain ⟨a1, g1, hv1, hl1⟩ := hn1
  -- the payload view, unseen, after closing
  have hlT : lnorm (TermClose.cl ρ η.wit 0 0 uu) = lnorm ty := by
    rw [← lnorm_sig (TermClose.cl ρ η.wit 0 0 uu), ← hsg, lnorm_sig]
  have hsT : shp (TermClose.cl ρ η.wit 0 0 uu) = shp ty := by
    rw [← shp_sig (TermClose.cl ρ η.wit 0 0 uu), ← hsg, shp_sig]
  have c1 := VR_close hc.unsee ρ uu [] 0 ρ ρ (shp ty) q (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have hvT : VR ρ (CE η.unsee) (TermClose.cl ρ η.wit 0 0 uu) (shp ty) q := c1.1 hvr
  have hV := Valid_of_VR _ (CE η.unsee) ρ q (fun _ _ _ h => h) (by rw [hlT]; exact hvd) (by rw [hsT]; exact hvT)
  have hVr : Valid ty q := Valid_of_sig hsg.symm hV
  have hwc : wc ty = some q.length := by
    rw [← wc_lnorm]
    cases hu : accs (lnorm ty) with
    | none => simp [wc, hu] at hwq
    | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
  have hQ := TermK2aLabsV.labsV_cnt (η := CE η.unsee) (fun _ _ _ h => h) hsg hwc hVr hvT i hiP w0q a1 g1 hw0q
    (hval.trans hv1)
  obtain ⟨f, hf, hle⟩ : ∃ f, η.pfr ga = some f ∧ f ≤ w0q.view := by
    rcases hQ with ⟨f, hf, hs | hle⟩ | ⟨B, hB⟩
    · exact (hs : False).elim
    · rw [hl1] at hf; exact ⟨f, hf, hle⟩
    · rw [hl1] at hB; exact absurd (hgb ▸ hB : (none : Option Box) = some B) (by simp)
  -- positions
  obtain ⟨w0, hp0, hv0, -, g0, hl0⟩ := ofArm_pos hq hw0q (hval.trans hv1)
  obtain ⟨w1P, hp1, -, hr1P, -, -⟩ := ofArm_pos hq1l hq1i hv1
  obtain ⟨u, m, hm, hloc, hmv, hu⟩ := hpos _ w1P hp1
  refine ⟨x0.label, B0, oi (lnorm ty) i, w0, hB0, hp0, ⟨a1, g0, hl0, hl1⟩, ⟨f, hf, by rw [hv0]; exact hle⟩,
    u, m, hm, hloc, ?_, ?_⟩
  · rw [hmv]; exact (getElem_val hWp.vals hp0 hp1).symm
  · rw [← hr1, ← hr1P]; exact hu

/-- A new binding whose counted words are box-load words and name `Gl` labels meets `StepOKX`. -/
theorem stepOKX_new {E : TEnv} {sto : Sto} {s : St} {a : AllocLabel} {Gl : AllocLabel → Prop} {th thP : TTh}
    {x : String} {rt : Ty} {ws : List Word}
    (he : thP.env = (x, rt, ws) :: th.env) (hst : thP.stack = th.stack)
    (hv : ∀ w ∈ pubWords rt ws, BoxLW E s.mem a w)
    (hl : ∀ w ∈ pubWords rt ws, ∀ l, Names l w → LblNew Gl th l) : StepOKX E sto s a Gl th thP := by
  have key : ∀ b ∈ Binds thP, b ∈ Binds th ∨ b = (x, rt, ws) := by
    intro b hb
    unfold TermK2a.Binds at hb
    rw [he, hst] at hb
    rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with e | hb
      · exact .inr e
      · exact .inl (TermK2a.mem_binds_env hb)
    · exact .inl (List.mem_append_right _ hb)
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rcases key b hb with h | rfl
    · exact .inl h
    · exact .inr fun w hw => .inr (.inr (hv w hw))
  · rcases key b hb with h | rfl
    · exact .inl h
    · exact .inr hl

/-- **`case` on a boxed scrutinee**, per result, with box loads: no box-load premise. -/
theorem sum_caseBX {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty}
    {ra rb : Ty} {ws : List Word} (hterm : th.term = .case a x e₁ y e₂)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hv : VR ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hS : (Ty.sum ra rb).tier = .boxed) (hsg : sig (.sum ra rb) = sig (TermClose.cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th))
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (hgb : η.box ga = none)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpa : PromAbove (stOf r.1 r.2.1 r.2.2))
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOKX (CE η) sto (stOf mem pairs th) ga Gl th r.2.2 := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, -, -, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hv
  have hvP := hv
  simp only [VR, shp] at hvP
  obtain ⟨n0, Ra, Rb, hR, hvP⟩ := hvP
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hvP.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hBP⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hBP
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (TermClose.cl ρ η.wit 0 0 u)) (sig (TermClose.cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := stOf mem pairs th) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0
    harm hus hnw.symm
  simp only [tstep, hterm, hea, List.mem_flatMap] at hr
  obtain ⟨r1, h1, h2⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    try simp only at h2
    split at h2
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 h2; exact injM_pa hpl1 hr2 hpa
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 h2; exact injM_pa hpl1 hr2 hpa
  obtain ⟨htag, hWp, -⟩ := (hpr r1 h1).2 hp1
  have hpos := projM_pos hrb hw hx0 h1
  have hn1 := TermStepper.projM_nalloc h1
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at htag hWp hpos hn1
  subst htag
  have key : ∀ (ty uu : Ty) (jP : Nat) (xv : String) (e : Expr), sig ty = sig (TermClose.cl ρ η.wit 0 0 uu) →
      (isBoxed ty = false → ∃ q, ofArm (lnorm ty) jP B0.pay = some q ∧ ShapeC (lnorm ty) q ∧
        wc (lnorm ty) ≠ none ∧ Valid (lnorm ty) q ∧ VR ρ η.unsee uu (shp ty) q) →
      ∀ r2 ∈ injM g s1 ty jP p1,
      (∀ l, FreshIn g th.nalloc r2.1.nalloc l → l ≠ ga) →
      (∀ l, FreshIn g th.nalloc r2.1.nalloc l →
        (∃ b ∈ (xv, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l) →
      (∀ l, FreshIn g th.nalloc r2.1.nalloc l →
        (∃ b ∈ (xv, ty, r2.2) :: th.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) →
      StepOKX (CE η) sto (stOf mem pairs th) ga Gl th
        (withS { th with term := e, env := (xv, ty, r2.2) :: th.env } r2.1) := by
    intro ty uu jP xv e hsgT hAT r2 h3 hfa hNf hGf
    cases hty : isBoxed ty with
    | true => exact stepOKX_of_stepOK (freshArm hn1 hty h3 hfa hNf hGf)
    | false =>
      rw [injM_nbB hty] at h3
      simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h3
      obtain ⟨q1, hq1, rfl⟩ := h3
      obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := hAT hty
      obtain ⟨q1P, hq1P, hs1, hw1, hv1, hvr1⟩ :=
        case_arm_nb hE.2.1 hty hsgT hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
      rw [hq1, Option.some.injEq] at hq1P
      subst hq1P
      have hwc1 : wc ty = some q1.length := by
        cases hu : accs ty with
        | none => simp [wc, hu] at hw1
        | some us => simp only [wc, hu, Option.map_some]; rw [hs1 us hu]
      have hBL := boxLW_arm hE.2.1 hgb hsgT hq hsq hwq hvd hvr hWp hq1 hB0 hpos
      have hLb := TermK2aLd.lbl_load (G := Gl) hE.2.1 hPf hBx hsgT hvr1 hwc1 hv1
      exact stepOKX_new rfl rfl hBL fun w hw l hn => .inl (hLb w hw l hn)
  by_cases hj : B0.tag < (armsOf ra).length
  · simp only [hj, ite_true, List.mem_map] at h2
    obtain ⟨r2, h3, rfl⟩ := h2
    exact key ra u B0.tag x e₁ hsg2.1 (hA hj).2 r2 h3 hfa hNf hGf
  · have hjP : (armsOf ra).length ≤ B0.tag := by omega
    simp only [hj, ite_false, List.mem_map] at h2
    obtain ⟨r2, h3, rfl⟩ := h2
    exact key rb v (B0.tag - (armsOf ra).length) y e₂ hsg2.2 (hBP hjP).2 r2 h3 hfa hNf hGf

/-- **`case`, every tier**, per result, with box loads (mirrors `tstepM_caseT`): non-boxed by
`sum_case`, boxed by `sum_caseBX`; no box-load premise. -/
theorem sum_caseTX {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (htv : TvOK cx)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th))
    (sto : Sto) {Gl : AllocLabel → Prop} {ga : AllocLabel} {N : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (hgb : η.box ga = none)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpa : PromAbove (stOf r.1 r.2.1 r.2.2))
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hNf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → N l)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l) :
    StepOKX (CE η) sto (stOf mem pairs th) ga Gl th r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | case hu _ _ _ _ =>
    obtain ⟨-, rt, ws, hea, hv, hl⟩ := use_FInv hu hi
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu htv).2.1
      have hsg := lay_closed (ρ := ρ) hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
      exact sum_caseBX hterm hea hv hS hsg hE hm sto hPf hBx hgb hr hpa hfa hNf hGf
    · refine stepOKX_of_stepOK (sum_case hterm (fun tP c₁P huP => ?_) hT hi htv sto Gl ga N r hr)
      rw [hu, Except.ok.injEq, Prod.mk.injEq] at huP; obtain ⟨rfl, rfl⟩ := huP
      rw [← tier_of_eskel hl.2.1]; exact hS

end TermK2aCaseB

#print axioms TermK2aCaseB.projM_pos
#print axioms TermK2aCaseB.boxLW_arm
#print axioms TermK2aCaseB.sum_caseBX
#print axioms TermK2aCaseB.sum_caseTX
