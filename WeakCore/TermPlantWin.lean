import WeakCore.TermPlant
import WeakCore.TermLocal
import WeakCore.TermCert
import WeakCore.TermZwIni

/-!
# TermPlantWin: the plant-window clause `PlantWinHeld` (draft)

`PlantMax`: at a planted label whose reader-visible count `ini` is below the
slot count, some unit of slot `ini` was neither initialised nor promised at the
plant (`Np` is the maximal held prefix and the plant sets `ini := max ini Np`).

* `plantMax_create`: the creation half at the plant.
-/

namespace TermPlantWin

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermPlant TermZwIni
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (creation) With `ini' = max (E0.ini l) (Np E0 s l) < Na`, some unit of slot `ini'`
is neither initialised (at `E0`) nor carries an outstanding promise of `s`. -/
theorem plantMax_create {E0 : TEnv} {s : St} {l : AllocLabel} {c : Cell} {Na : Nat} {e : Ty}
    {us : List Acc} (hc : E0.sto l = some c) (hT : c.ty = .array (.lit Na) e) (hus : accs e = some us)
    {ini' : Nat} (hini : ini' = max (E0.ini l) (Np E0 s l)) (hlt : ini' < Na) :
    ∃ o, ini' * nWords us ≤ o ∧ o < (ini' + 1) * nWords us ∧ ¬ InitR E0 c l o ∧
      ∀ u ∈ s.promises, ∀ m, s.mem[u]? = some m → m.loc ≠ ⟨l, o⟩ := by
  have hnp : ¬ PrefixHeld E0 s l c (ini' + 1) := fun hp => by
    have := le_Np hc hT (by omega) hp
    omega
  have hex : ∃ o, o < (ini' + 1) * nWords us ∧ ¬ InitR E0 c l o ∧
      ¬ ∃ u ∈ s.promises, ∃ m, s.mem[u]? = some m ∧ m.loc = ⟨l, o⟩ := by
    refine Classical.byContradiction fun hne => hnp fun Na' e' us' hT' hus' o ho => ?_
    rw [hT] at hT'
    cases hT'
    rw [hus] at hus'
    cases hus'
    refine Classical.byContradiction fun hno => hne ⟨o, ho, fun hI => hno (Or.inl hI), fun hP => hno (Or.inr hP)⟩
  obtain ⟨o, ho, hnI, hnP⟩ := hex
  have hph := PrefixHeld_Np (s := s) hc
  refine ⟨o, ?_, ho, hnI, fun u hu m hm hl => hnP ⟨u, hu, m, hm, hl⟩⟩
  refine Classical.byContradiction fun hge => ?_
  have hlt' : o < ini' * nWords us := by omega
  rcases Nat.le_total (Np E0 s l) (E0.ini l) with h | h
  · have e1 : ini' = E0.ini l := by omega
    exact hnI fun N' e' us' h1 h2 => by
      rw [hT] at h1; cases h1; rw [hus] at h2; cases h2; rw [← e1]; exact hlt'
  · have e1 : ini' = Np E0 s l := by omega
    rcases hph Na e us hT hus o (by rw [← e1]; exact hlt') with hI | hP
    · exact hnI hI
    · exact hnP hP

#print axioms plantMax_create

/-- A units store whose first unit is a single word and which appends nothing
fulfils an own promise at its first address. -/
theorem storeUnits_first_ful {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St}
    (hs : s' ∈ storeUnits k arch pw a rel (.one :: us) ws i s) (hm : s'.mem = s.mem) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc = offs a i := by
  cases ws with
  | nil => simp [storeUnits] at hs
  | cons w ws =>
  simp only [storeUnits, List.mem_flatMap] at hs
  obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
  have hg := TermFul.storeUnits_grow us ws (i + 1) _ s' hs
  have hsz := TermFul.memExt_size hg.1
  obtain ⟨t, hcase, -⟩ := stepStore_casesC hst
  rcases hcase with ⟨e1, -, -⟩ | ⟨-, ht, -, -, m, hm1, hl, -⟩
  · exfalso
    simp only at hsz
    rw [hm, e1, Array.size_push] at hsz
    omega
  · exact ⟨t, m, ht, hm1, hl⟩

/-- A two-word first unit always appends. -/
theorem storeUnits_two_grow {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St}
    (hs : s' ∈ storeUnits k arch pw a rel (.two :: us) ws i s) : s'.mem ≠ s.mem := by
  intro hm
  match ws, hs with
  | w0 :: w1 :: ws, hs =>
    simp only [storeUnits] at hs
    have hg := TermFul.storeUnits_grow us ws (i + 2) _ s' hs
    have hsz := TermFul.memExt_size hg.1
    simp only [Promises.stepStorePair, Array.size_push] at hsz
    rw [hm] at hsz
    omega

#print axioms storeUnits_first_ful
#print axioms storeUnits_two_grow

/-- **A no-append `bufInit` step fulfils an own promise at the slot's first unit** (positive width). -/
theorem bufInit_tstep_ful {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {b ia v : At}
    {e : Expr} (hterm : th.term = .let_ x (.bufInit b ia v) e)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hm : r.1 = mem)
    {rt : Ty} {w : Word} {ad : Address} {rti : Ty} {wi : Word} {n : Nat}
    (hb : evalAt th.env b = some (rt, [w])) (hw : w.val = .loc ad 0)
    (hi : evalAt th.env ia = some (rti, [wi])) (hn : numOf [wi] = some n)
    {μ : Mode} {u : Ty} {us : List Acc} (hbe : bufElem rt = some (μ, u)) (hus : accs u = some us)
    (hpos : 0 < nWords us) :
    ∃ t m, t ∈ th.promises ∧ mem[t]? = some m ∧ m.loc = offs ad (n * nWords us) := by
  rw [TermLocal.tstep_let_gen hterm rfl] at hr
  obtain ⟨⟨s', t', ws'⟩, hev, rfl⟩ := List.mem_map.1 hr
  simp only at hm
  have ha : addrOf w = some ad := by simp [addrOf, hw]
  simp only [evalOp] at hev
  rw [hb, hi] at hev
  cases hv : evalAt th.env v with
  | none => rw [hv] at hev; simp at hev
  | some p =>
  obtain ⟨tv, xs⟩ := p
  rw [hv] at hev
  simp only [hbe, hn, ha, hus] at hev
  cases rt with
  | refine t0 ψ =>
    cases t0 with
    | loc μ' a0 =>
      cases a0 with
      | array n' e' =>
        simp only [] at hev
        obtain ⟨s'', hs'', e1⟩ := List.mem_map.1 hev
        simp only [Prod.mk.injEq] at e1
        obtain ⟨rfl, -, -⟩ := e1
        match us, hs'', hpos with
        | [], _, hp => simp [nWords] at hp
        | .one :: us', hs, _ =>
            obtain ⟨t, m, ht, hm1, hl⟩ := storeUnits_first_ful hs hm
            exact ⟨t, m, ht, hm1, by rw [hl]; simp [offs]⟩
        | .two :: us', hs, _ => exact absurd hm (storeUnits_two_grow hs)
      | _ => simp at hev
    | _ => simp at hev
  | _ => simp at hev

#print axioms bufInit_tstep_ful

/-- `IniR` holds vacuously of the empty value. -/
theorem IniR_nil (ρ : Nat → Nat) (ini : AllocLabel → Nat) (ψ : Pred) : IniR ρ ini ψ [] := by
  induction ψ <;> simp_all [IniR]

/-- **The empty value is env-independent**: `VR` at `[]` reads only the relations,
witnesses and program (every reference, code, boxed or tagged case needs a word). -/
theorem VR_nil_congr : ∀ (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp),
    η₁.rels = η₂.rels → η₁.wit = η₂.wit → η₁.prog = η₂.prog →
    VR ρ η₁ t rt [] → VR ρ η₂ t rt []
  | .tvar k, η₁, η₂, ρ, rt, hr, _, _, hv => by
      simp only [VR, TEnv.get] at hv ⊢; rw [← hr]; exact hv
  | .refine t ψ, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv ⊢
      exact ⟨VR_nil_congr t η₁ η₂ ρ rt hr hw hp hv.1, IniR_nil _ _ _⟩
  | .iex b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, w, h1, h2⟩ := hv
      exact ⟨n, rb, w, h1, VR_nil_congr b η₁ η₂ (vcons w ρ) rb hr hw hp h2⟩
  | .prod a b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR, List.take_nil, List.drop_nil] at hv ⊢
      obtain ⟨ra, rb, h1, hf⟩ := hv
      refine ⟨ra, rb, h1, fun n hn' => ?_⟩
      obtain ⟨e1, e2, e3⟩ := hf n hn'
      exact ⟨e1, VR_nil_congr a η₁ η₂ ρ _ hr hw hp e2, VR_nil_congr b η₁ η₂ ρ _ hr hw hp e3⟩
  | .sum a b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv
      obtain ⟨n, Ra, Rb, h1, ⟨hb, x, s, B, hx, -⟩ | ⟨j, p, hd, -⟩⟩ := hv
      · simp at hx
      · cases h : (Ty.sum Ra Rb).tier <;> rw [h] at hd <;> simp [decodeArm] at hd
  | .code a b _, η₁, η₂, ρ, rt, _, hw, hp, hv => by
      simp only [VR] at hv ⊢; rw [← hw, ← hp]; exact hv
  | .tex κ b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv ⊢
      obtain ⟨n, rb, s, h1, h2, haf, h3⟩ := hv
      refine ⟨n, rb, s, h1, h2, haf, VR_nil_congr b (η₁.push0 s) (η₂.push0 s) ρ rb ?_ ?_ ?_ h3⟩
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hr]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
      · simpa only [TEnv.push0, TEnv.ins, TEnv.insR] using hp
  | .ptr μ u, η₁, η₂, ρ, rt, _, _, _, hv => by
      simp only [VR] at hv
      obtain ⟨a, c, h1, -⟩ := hv; simp at h1
  | .ptrOpt μ u, η₁, η₂, ρ, rt, _, _, _, hv => by
      simp only [VR] at hv
      rcases hv with h1 | ⟨a, c, h1, -⟩ <;> simp at h1
  | .loc μ u, η₁, η₂, ρ, rt, _, _, _, hv => by
      simp only [VR] at hv
      rcases hv with ⟨h1, -⟩ | ⟨a, c, U, h1, -⟩ <;> simp at h1
  | .intS _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .int, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .fix _ _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .lanes _ _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .unit, _, _, _, _, _, _, _, _ => by simp [VR]
  | .void, _, _, _, _, _, _, _, hv => by simp [VR] at hv
  | .array _ _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .share _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .cap _ _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word _ _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok _ _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .word2 _ _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .epair _ _, _, _, _, _, _, _, _, hv => by simpa only [VR] using hv
  | .tokE _ _ _, _, _, _, _, _, _, _, _ => by simp [VR]
  | .mu b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv ⊢
      rw [← hw]
      refine VR_nil_congr b (η₁.push0 (cl ρ η₁.wit 0 0 (.mu b))) (η₂.push0 (cl ρ η₁.wit 0 0 (.mu b)))
        ρ rt ?_ ?_ ?_ hv
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hr]
      · simp only [TEnv.push0, TEnv.ins, TEnv.insR, hw]
      · simpa only [TEnv.push0, TEnv.ins, TEnv.insR] using hp
  | .iall b, η₁, η₂, ρ, rt, hr, hw, hp, hv => by
      simp only [VR] at hv ⊢
      exact fun n => VR_nil_congr b η₁ η₂ (vcons n ρ) rt hr hw hp (hv n)

/-- A zero-width value held in the thread's view inhabits its type in the bare
environment of the program (`InhZ`). -/
theorem inhZ_of_envVal {η : TEnv} {T : Ty} {ws : List Word} (h : EnvVal (CE η) T ws)
    (h0 : ws.length = 0) : InhZ η.prog T := by
  obtain rfl := List.eq_nil_of_length_eq_zero h0
  exact ⟨[], ⟨VR_nil_congr T (CE (CE η)) _ _ _ rfl rfl rfl h.1, h.2⟩, rfl⟩

#print axioms IniR_nil
#print axioms VR_nil_congr
#print axioms inhZ_of_envVal

set_option maxHeartbeats 1600000 in
/-- **BH1** (the first conjunct of `bufInitHeld`): a `bufInit` at a frontier buffer
writes a slot below `ini`. Positive width: the step appends nothing (`plantFulfil`), so
its first unit fulfils an own promise, which `promIni` puts below `ini`; zero width:
`ZwIni` with `k < n`. -/
theorem bh1_of {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.bufInit b i v) e)
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx)
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hful : OwnFrOp (CE η) cx th → r.1 = mem)
    (hpi : PromIniE (CE η) (stOf mem pairs th)) {Pd : AllocLabel → Prop} (hzw : ZwIniE (CE η) Pd)
    (hnp : ∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → ¬ Pd ad.label) :
    ∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
      evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
      (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label := by
  intro rt0 w0 ad0 rti0 wi0 n0 hb0 hw0 hi0 hn0 hpf0 hrc0
  have hterm0 := hterm
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨rb, wsb, Rb, Rr1, hea, hvb, hlb, hvrb, hi1, hle1⟩ := useR hu hi hE.2.2
  obtain ⟨rv, wsv, Rv, Rr2, hev, hvv, hlv, hvrv, hi2, hle2⟩ := useR hu2 hi1 hE.2.2
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1.1
  obtain ⟨ti, hpi', hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VR hi1.1.2.1 hpi'
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
  simp only [VR] at hvb
  obtain ⟨hv, hir⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hown, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  -- identify the quantified values with the typed ones
  rw [hea] at hb0
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hb0
  obtain ⟨rfl, rfl⟩ := hb0
  rw [hwv] at hw0
  simp only [WeakMem.Val.loc.injEq, and_true] at hw0
  subst hw0
  rw [hei] at hi0
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hi0
  obtain ⟨rfl, rfl⟩ := hi0
  have hni : numOf [wi] = some (ev ρ j) := by simp [numOf, hwi]
  rw [hni] at hn0
  cases hn0
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us :=
    (accs_rtW hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  obtain ⟨R0, H0, -, hent0, -⟩ := MemHeld_focus hH ad.label
  obtain ⟨hTc, hoff⟩ := bufCell hent0 hsto hat hini
  have hJN : ev ρ j < ev ρ n := by omega
  by_cases hw : 0 < nWords us
  · -- positive width: the first unit's fulfilled promise is below `ini`
    have hof : OwnFrOp (CE η) cx th := by
      refine ⟨Or.inl ⟨x, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, i, v, hterm0⟩))))⟩, ad.label, hpf0, ?_⟩
      exact ⟨b, _, w, ad, 0, by rw [hterm0]; rfl, hea, hwv, rfl⟩
    obtain ⟨t1, m1, ht1, hm1, hl1⟩ := bufInit_tstep_ful hterm0 hr (hful hof) hea hwv hei hni rfl hus hw
    have hI := hpi t1 m1 ht1 hm1 c (by rw [hl1]; exact hsto) (by rw [hl1]; exact hpf0)
    rw [hl1] at hI
    have h2 := hI _ _ _ hTc hweA
    simp only [offs, hoff, Nat.zero_add] at h2
    exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_refl _) h2)
  · -- zero width: the written value is empty, so the element type is inhabited
    obtain ⟨hval, hlen⟩ := ownStoreVal (cx := c₁) hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1
      hvv hlv hsig hus
    have hinh : InhZ (CE η).prog (cl ρ η.wit 0 0 u) :=
      inhZ_of_envVal hval (by rw [hlen]; omega)
    have h2 := hzw ad.label c _ _ us hpf0 (hnp _ _ _ hea hwv) hsto hTc hweA (by omega) hinh
    omega

#print axioms bh1_of

end TermPlantWin
