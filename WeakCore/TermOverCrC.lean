import WeakCore.TermOverCrZ
import WeakCore.TermPieceCov

/-!
# TermOverCrC: the foreign case of the credited cover at a thread step (Cfg layer)

Along thread `i`'s step, an idle thread `j`'s own frontier cell `l` keeps its environment
(cell, counts, frontier: `own_agree`), and every cut's skip list at the shared label `l` is the
same set before and after (`promAt_congr`, `stepper_set_post`).  These discharge the
environment premises of `foreign_overCrH` / `foreign_overCrPZ` at the configuration level.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **An idle thread's own frontier cell is untouched by another thread's step**: its cut cell,
counts and frontier are the old ones. -/
theorem own_agree {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hgf : GFoot g Eg Eg2 n n' v)
    (hfr : GFreshE g Eg n n') {j : Nat} (hji : j ≠ g.i) (S : AllocLabel → Prop) {l : AllocLabel} {cl : Cell}
    (hc2 : cutSto Eg2 j l = some cl) (hown : cl.owner = some j) :
    cutSto Eg j l = some cl ∧ Eg.sto l = some cl ∧ Eg2.sto l = Eg.sto l ∧ Eg2.ini l = Eg.ini l ∧
      Eg2.rini l = Eg.rini l ∧ Eg2.pfr l = Eg.pfr l := by
  have hO := Cut_other hgf hji S
  have hpre : cutSto Eg j l = some cl := by
    cases e : cutSto Eg j l with
    | none =>
        obtain ⟨-, ho, -⟩ := hO.2 l cl hc2 e
        rw [hown] at ho
        exact absurd (Option.some.inj ho) hji
    | some c1 =>
        have h2 : cutSto Eg2 j l = some c1 := hO.1.sto l c1 e
        rw [hc2] at h2
        rw [Option.some.inj h2]
  have hs : Eg.sto l = some cl := cutSto_sub hpre
  have hnf : ¬ FreshIn g n n' l := fun hF => by rw [(hfr l hF).1] at hs; cases hs
  have hno : ¬ Eg.OwnAt g.i l := fun ⟨c2, h1, h2⟩ => by
    rw [hs] at h1
    cases h1
    rw [hown] at h2
    exact hji (Option.some.inj h2)
  obtain ⟨-, hsto, -, hini, hpfr, -, hrini⟩ := hgf
  refine ⟨hpre, hs, ?_, ?_, ?_, ?_⟩
  · rcases hsto l with e | ⟨hF, -⟩
    · exact e
    · exact absurd hF hnf
  · rcases (hini l).2 with e | hF | hO'
    · exact e
    · exact absurd hF hnf
    · exact absurd hO' hno
  · rcases hrini l with e | hF | hO'
    · exact e
    · exact absurd hF hnf
    · exact absurd hO' hno
  · rcases hpfr l with e | ⟨-, -, -, -, hO'⟩ | ⟨hF, -⟩
    · exact e
    · exact absurd hO' hno
    · exact absurd hF hnf

#print axioms own_agree

/-- **Skip lists agree** at a visible label where two cuts see the same cell, counts and
frontier, over the same memory, with the same promise set (own plus footprint). -/
theorem promAt_congr {E1 E2 : TEnv} {s1 s2 : St} {a : Address}
    (hs : E2.sto a.label = E1.sto a.label) (hp : E2.pfr a.label = E1.pfr a.label)
    (hi : E2.ini a.label = E1.ini a.label) (hr : E2.rc a.label = E1.rc a.label)
    (hv1 : Vis E1 a.label) (hv2 : Vis E2 a.label) (hm : s2.mem = s1.mem)
    (hset : ∀ t, t ∈ s2.promises ++ E2.fp ↔ t ∈ s1.promises ++ E1.fp) (t : Ts) :
    t ∈ PromAt E2 s2 a ↔ t ∈ PromAt E1 s1 a := by
  have hVU : VisU E2 a ↔ VisU E1 a := by
    unfold VisU
    exact ⟨fun h => ⟨(WordUnit_congr hs).1 h.1, hv1⟩, fun h => ⟨(WordUnit_congr hs).2 h.1, hv2⟩⟩
  have hPU : PredU E2 a ↔ PredU E1 a := by
    unfold PredU
    rw [hp, IniW_congrU hs hi, IniWr_congr hs hr]
  have hf1 : FpAt E1 a = E1.fp := by unfold FpAt; simp only [hv1, ↓reduceIte]
  have hf2 : FpAt E2 a = E2.fp := by unfold FpAt; simp only [hv2, ↓reduceIte]
  by_cases hv : VisU E1 a
  · have hv' := hVU.2 hv
    simp only [PromAt, hv, hv', ↓reduceIte]
  · have hv' : ¬ VisU E2 a := fun h => hv (hVU.1 h)
    by_cases hq : PredU E1 a
    · have hq' := hPU.2 hq
      simp only [PromAt, hv, hv', hq, hq', ↓reduceIte, hf1, hf2, List.mem_filter]
      rw [hm]
      exact ⟨fun h => ⟨(hset t).1 h.1, h.2⟩, fun h => ⟨(hset t).2 h.1, h.2⟩⟩
    · have hq' : ¬ PredU E2 a := fun h => hq (hPU.1 h)
      simp only [PromAt, hv, hv', hq, hq', ↓reduceIte, hf1, hf2]
      exact hset t

#print axioms promAt_congr

/-- **The stepper's old footprint with its new promises is every promise after the step.** -/
theorem stepper_set_post {Eg : GEnv} {c c' : Cfg} {i : Nat} {th th' : TTh}
    (hP : PromsOK Eg c) (hD : PromsDisj c) (hF : FpOwnFree Eg c)
    (hi : c.ths[i]? = some th) (hi' : c'.ths[i]? = some th') (ho : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?)
    (t : Ts) : t ∈ th'.promises ++ Eg.fpOf i ↔ t ∈ allProms c' := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact mem_allProms.2 ⟨i, th', hi', h⟩
    · obtain ⟨j, thj, hj, htj⟩ := mem_allProms.1 ((hP i th hi t).1 (List.mem_append_right _ h))
      by_cases hji : j = i
      · subst hji
        rw [hi] at hj
        cases hj
        exact absurd htj (hF j th t hi h)
      · exact mem_allProms.2 ⟨j, thj, by rw [ho j hji]; exact hj, htj⟩
  · intro h
    rcases (mem_allProms_upd hi' ho).1 h with h | ⟨j, thj, hji, hj, htj⟩
    · exact List.mem_append_left _ h
    · rcases List.mem_append.1 ((hP i th hi t).2 (mem_allProms.2 ⟨j, thj, hj, htj⟩)) with h1 | h1
      · exact absurd (hD j i thj th t hji hj hi htj h1) id
      · exact List.mem_append_right _ h1

#print axioms stepper_set_post

/-- The targets of the entries at label `l` only. -/
def tgL (l : AllocLabel) (tg : TermPiece.GdE → Option Ts) (g : TermPiece.GdE) : Option Ts :=
  if g.l = l then tg g else none

theorem tgL_some {l : AllocLabel} {tg : TermPiece.GdE → Option Ts} {g : TermPiece.GdE} {t : Ts}
    (h : tgL l tg g = some t) : g.l = l ∧ tg g = some t := by
  unfold tgL at h
  by_cases hg : g.l = l
  · simp only [hg, ↓reduceIte] at h
    exact ⟨hg, h⟩
  · simp only [hg, ↓reduceIte] at h
    cases h

theorem tgL_of {l : AllocLabel} {tg : TermPiece.GdE → Option Ts} {g : TermPiece.GdE} (hg : g.l = l) :
    tgL l tg g = tg g := by
  unfold tgL
  simp only [hg, ↓reduceIte]

/-- The drop items at `l` read only the targets at `l`. -/
theorem dnOf_tgL (l : AllocLabel) (tg : TermPiece.GdE → Option Ts) (Kf : TermPiece.GdE → Nat → Bool)
    (Gd : List TermPiece.GdE) : dnOf l (tgL l tg) Kf Gd = dnOf l tg Kf Gd := by
  unfold dnOf
  congr 1
  funext g
  by_cases hg : g.l = l
  · simp only [hg, ↓reduceIte, tgL_of hg]
  · simp only [hg, ↓reduceIte]

/-- `plantD1` reads the targets only through the entries targeting `t`. -/
theorem plantD1_congr {Gd : List TermPiece.GdE} {R : TermPiece.GdE → Res} {tg1 tg2 : TermPiece.GdE → Option Ts}
    {t : Ts} (h : ∀ g ∈ Gd, tg1 g = some t ↔ tg2 g = some t) :
    TermPlant.plantD1 Gd R tg1 t = TermPlant.plantD1 Gd R tg2 t := by
  unfold TermPlant.plantD1
  have e : Gd.find? (fun g => decide (tg1 g = some t)) = Gd.find? (fun g => decide (tg2 g = some t)) := by
    clear R
    induction Gd with
    | nil => rfl
    | cons g Gs ih =>
        have hg := h g (List.mem_cons_self ..)
        have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
        by_cases h1 : tg1 g = some t
        · have h2 := hg.1 h1
          simp only [List.find?_cons, h1, h2, decide_true]
        · have h2 : ¬ tg2 g = some t := fun h2 => h1 (hg.2 h2)
          simp only [List.find?_cons, h1, h2, decide_false, ih']
  rw [e]

/-- At a timestamp whose message is at `l`, the targets at `l` pay what all targets pay, when
each target's message is at its entry's label. -/
theorem plantD1_tgL {Gd : List TermPiece.GdE} {R : TermPiece.GdE → Res} {tg : TermPiece.GdE → Option Ts}
    {M : Memory} {l : AllocLabel}
    (hlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → M[t]? = some m → m.loc.label = g.l)
    {t : Ts} {m : Msg} (hm : M[t]? = some m) (hl : m.loc.label = l) :
    TermPlant.plantD1 Gd R (tgL l tg) t = TermPlant.plantD1 Gd R tg t := by
  refine plantD1_congr fun g hg => ⟨fun h => (tgL_some h).2, fun h => ?_⟩
  have hgl : g.l = l := by rw [← hlab g hg t m h hm, hl]
  rw [tgL_of hgl]
  exact h

/-- The credited cover reads the credit only at timestamps whose message is at `l`. -/
theorem overCrE_congrL {E : TEnv} {s : St} {cr cr2 : Ts → Res} {l : AllocLabel} {c : Cell}
    (hcr : ∀ t m, s.mem[t]? = some m → m.loc.label = l → cr t = cr2 t)
    (h : TermOverCr.OverCrE E s cr l c) : TermOverCr.OverCrE E s cr2 l c := by
  obtain ⟨Gs, ⟨hnd, hit, hcv, hwa, hlast⟩, hHL⟩ := h
  refine ⟨Gs, ⟨hnd, fun x hx => ?_, hcv, hwa, fun t m ht hm hl hnw hz => ?_⟩, hHL⟩
  · have hx' := hit x hx
    obtain ⟨mh, _, hmh, hlab, _⟩ := id hx'
    refine crItemQ_mono ?_ hx'
    rw [hcr x.1 mh hmh hlab]
    exact Res.le_refl _
  · exact hlast t m ht hm hl hnw (by rw [hcr t m hm hl]; exact hz)

/-- A closed buffer type's element type is closed. -/
theorem Clo_arr {N : Idx} {e : Ty} (h : Clo (.array N e)) : Clo e := by
  have h1 := h.1
  simp only [tb] at h1
  refine ⟨h1, fun ρ W a b => ?_⟩
  have := h.2 ρ W a b
  simp only [cl, Ty.array.injEq] at this
  exact this.2

/-- **A typed word lies in a piece of its cell** (closed, guarded cell type). -/
theorem piece_of_wordOK {E : TEnv} {T : Ty} {o : Nat} {w : Word} (hc : Clo T) (hm : mg T = true)
    (hw : WordOK E T o w) :
    ∃ b S us, TermPiece.Piece T b S ∧ accs S = some us ∧ b ≤ o ∧ o < b + nWords us := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨-, hsh⟩, hw0, -, hbo⟩ := hw
  have ho' : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  rcases hseg with ⟨rfl, rfl, hA⟩ | ⟨N, us, jj, rfl, hus, hj, rfl⟩
  · obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.1 hA
    have hl := hsh L hL
    exact TermPieceCov.piece_cover hc hm hL (by omega)
  · have hl := hsh us hus
    have hm' : mg S = true := by simpa [mg] using hm
    have hle : (jj + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at hle
    exact TermPieceCov.piece_cover_arr (Clo_arr hc) hm' hus (by omega)

#print axioms piece_of_wordOK

/-- **`hent_ofC` at an abstract guard `Gw`**: the target premise `htg` is asked under `Gw`
(the pre- or post-step window), and under the cover mask `L0`.  `hent_ofC`, `hent_ofCO` and
`hent_ofCOW` are its corollaries. -/
theorem hent_ofG {E E' Ek : TEnv} {s s' sk : St} {l : AllocLabel} {c ck : Cell} {lt ot n : Nat}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE} {L0 : Nat → Bool} {Gw : Nat → Ts → Prop}
    (hmemk : sk.mem = s.mem)
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hleft : ∀ o, ¬ VisU E' ⟨l, o⟩ → ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      t ∈ PromAt E s ⟨l, o⟩ →
      t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o)
    (hcov : ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), Ek.sto lt = some c →
      c.owner ≠ some Ek.tid → TermPiece.Piece c.ty b S → accs S = some vs → t ∈ Ek.fp → sk.mem[t]? = some m →
      m.loc.label = lt → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → ot ≤ m.loc.offset →
      ot + n > m.loc.offset → L0 (m.loc.offset - ot) = true → ∃ g ∈ Gd, g.l = lt ∧ g.b = b ∧ g.S = S)
    (hstok : Ek.sto l = some ck) (hty : ck.ty = c.ty) (hownk : ck.owner ≠ some Ek.tid)
    (hfp : ∀ t, t ∈ s.promises → t ∈ Ek.fp)
    (hpiece : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧
      b ≤ o ∧ o < b + nWords us)
    (hsing : ∀ o tw b S us i, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPiece.Piece c.ty b S → accs S = some us →
      b ≤ o → InAcc us i (o - b) → ∀ o', InAcc us i o' → o' = o - b)
    (hL : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true)
    (hL0 : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → L0 (o - ot) = true)
    (htg : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → Gw o tw →
      ¬ VisU E' ⟨l, o⟩ → ∀ us, accs g.S = some us →
      g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    ∀ o tw, ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw → Gw o tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true := by
  intro o tw hv' hl hov hno hw
  obtain ⟨hlt, ho1, ho2⟩ := newOver_inTgt hfoot hpre (hleft o hv') hov hno
  have hL' := hL hlt
  have hL0' := hL0 hlt
  subst hlt
  obtain ⟨b, S, us, hP, hus, hb1, hb2⟩ := hpiece o tw hl
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hl
  have hmwk : sk.mem[tw]? = some mw := by rw [hmemk]; exact hmw
  obtain ⟨g, hg, hgl, hgb, hgS⟩ := hcov ck b S us tw mw hstok hownk (by rw [hty]; exact hP) hus (hfp tw htw)
    hmwk (by rw [hml]) (by rw [hml]; exact hb1) (by rw [hml]; exact hb2) (by rw [hml]; exact ho1)
    (by rw [hml]; exact ho2) (by rw [hml]; exact hL0' o tw ho1 ho2 hov hno)
  subst hgb hgS
  obtain ⟨i, hi⟩ := inAcc_ex us (o - g.b) (Nat.sub_lt_left_of_lt_add hb1 hb2)
  exact ⟨g, hg, hgl, htg g hg hgl o tw hl hw hv' us hus hb1 hb2,
    us, i, hus, hb1, hi, hsing o tw g.b g.S us i hl hP hus hb1 hi, hL' o tw ho1 ho2 hov hno g hg hgl hb1⟩

#print axioms hent_ofG

/-- **(hent, guarded)** `hent_of` with the piece cover and the single-word property asked only at
units holding an own promise (`LowOwn`), and the mask premise only when the target is at `l`. -/
theorem hent_ofC {E E' Ek : TEnv} {s s' sk : St} {l : AllocLabel} {c ck : Cell} {lt ot n : Nat}
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hmemk : sk.mem = s.mem)
    (hfoot : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
      m.loc.label = lt ∧ ot ≤ m.loc.offset ∧ ot + n > m.loc.offset)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hleft : ∀ o, ¬ VisU E' ⟨l, o⟩ → ∀ t m, t < s.mem.size → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      t ∈ PromAt E s ⟨l, o⟩ →
      t ∉ PromAt E' s' ⟨l, o⟩ → lt = l ∧ ot ≤ o ∧ ot + n > o)
    (hcov : ∀ (c : Cell) (b : Nat) (S : Ty) (vs : List Acc) (t : Ts) (m : Msg), Ek.sto lt = some c →
      c.owner ≠ some Ek.tid → TermPiece.Piece c.ty b S → accs S = some vs → t ∈ Ek.fp → sk.mem[t]? = some m →
      m.loc.label = lt → b ≤ m.loc.offset → b + nWords vs > m.loc.offset → ot ≤ m.loc.offset →
      ot + n > m.loc.offset → ∃ g ∈ Gd, g.l = lt ∧ g.b = b ∧ g.S = S)
    (hstok : Ek.sto l = some ck) (hty : ck.ty = c.ty) (hownk : ck.owner ≠ some Ek.tid)
    (hfp : ∀ t, t ∈ s.promises → t ∈ Ek.fp)
    (hpiece : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → ∃ b S us, TermPiece.Piece c.ty b S ∧ accs S = some us ∧
      b ≤ o ∧ o < b + nWords us)
    (hsing : ∀ o tw b S us i, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPiece.Piece c.ty b S → accs S = some us →
      b ≤ o → InAcc us i (o - b) → ∀ o', InAcc us i o' → o' = o - b)
    (hL : lt = l → ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ¬ TermPlant.OverT E s ⟨l, o⟩ tw → ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true)
    (htg : ∀ g ∈ Gd, g.l = l → ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermOverCr.WinG E' s' l o tw →
      ∀ us, accs g.S = some us →
      g.b ≤ o → o < g.b + nWords us → ∃ t, tg g = some t) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true := by
  intro o tw _ hv' hl hw hov hno
  exact hent_ofG (L0 := fun _ => true) (Gw := TermOverCr.WinG E' s' l) hmemk hfoot hpre hleft (fun c b S vs t m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 _ => hcov c b S vs t m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
    hstok hty hownk hfp hpiece hsing hL (fun _ _ _ _ _ _ _ => rfl) (fun g hg hgl o tw hl hw _ => htg g hg hgl o tw hl hw) o tw hv' hl hov hno hw

#print axioms hent_ofC

/-- Predicted units agree where the cell, frontier, counts agree. -/
theorem predU_congr {E1 E2 : TEnv} {a : Address} (hs : E2.sto a.label = E1.sto a.label)
    (hp : E2.pfr a.label = E1.pfr a.label) (hi : E2.ini a.label = E1.ini a.label)
    (hr : E2.rc a.label = E1.rc a.label) : PredU E2 a ↔ PredU E1 a := by
  unfold PredU
  rw [hp, IniW_congrU hs hi, IniWr_congr hs hr]

end TermOverCrW
