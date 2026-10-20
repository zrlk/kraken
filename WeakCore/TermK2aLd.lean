import WeakCore.TermK2aLoad

/-!
# K-2a loads: per-operation binding contracts

The counted words of a value depend only on its runtime signature (`pubWords_sig`), so a loaded
binding at runtime type `ru` (with `sig ru = sig (cl ρ W 0 0 u)`) counts the words its cell
component counts; `TermK2aLoad.valB_of_reads` then gives the step's binding contract.
-/

namespace TermK2aLd

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermClose (cl tb arrFree_cl)
open TermCut (GEnv)

/-! ## 1. Counted words are signature-invariant -/

theorem pubWords_skel : ∀ (t : Ty),
    (∀ ws, pubWords (skel t) ws = pubWords t ws) ∧ (∀ j p, pubArm (skel t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      have hs := sNo_skel (.prod a b)
      simp only [skel] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (skel a) (skel b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, wc_skel, iha.1, ihb.1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have hs := sNo_skel (.sum a b)
      have ht := tier_skel (.sum a b)
      have hl := lnorm_skel (.sum a b)
      simp only [skel] at hs ht hl ⊢
      have hal : (armsOf (skel a)).length = (armsOf a).length := by rw [armsOf_skel, List.length_map]
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
      · simp only [pubArm, hal, iha.2, ihb.2]
  | refine t ψ ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [skel]
        rw [pubWords_refine, ← ih.1]
        cases h : skel t <;> first | rfl | (simp only [rf]; rw [pubWords_refine])
      · simp only [skel]
        rw [show pubArm (.refine t ψ) j p = pubArm t j p by simp only [pubArm], ← ih.2]
        cases h : skel t <;> first | rfl | (simp only [rf, pubArm]; done) | simp only [rf]
  | iall t ih =>
      have hs := sNo_skel (.iall t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iex t ih =>
      have hs := sNo_skel (.iex t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | mu t ih =>
      have hs := sNo_skel (.mu t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | tex κ t ih =>
      have hs := sNo_skel (.tex κ t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | array i e _ =>
      have hs := sNo_skel (.array i e)
      simp only [skel] at hs ⊢
      have h1 : ∀ ws, pubWords (.array (.lit 0) (skel e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ =>
      exact ⟨fun ws => by simp only [skel, pubWords, sNo, mPub_skelM]; rfl,
        fun j p => by simp only [skel, pubArm, pubWords, sNo, mPub_skelM]; rfl⟩
  | ptrOpt μ u _ =>
      exact ⟨fun ws => by simp only [skel, pubWords, sNo, mPub_skelM]; rfl,
        fun j p => by simp only [skel, pubArm, pubWords, sNo, mPub_skelM]; rfl⟩
  | loc μ u _ =>
      exact ⟨fun ws => by simp only [skel, pubWords, sNo, mPub_skelM]; rfl,
        fun j p => by simp only [skel, pubArm, pubWords, sNo, mPub_skelM]; rfl⟩
  | code a b _ _ =>
      exact ⟨fun ws => by simp only [skel, pubWords, sNo], fun j p => by simp only [skel, pubArm, pubWords, sNo]⟩
  | _ => exact ⟨fun ws => by simp [skel, pubWords, sNo], fun j p => by simp [skel, pubArm, pubWords, sNo]⟩

theorem pubWords_er : ∀ (t : Ty),
    (∀ ws, pubWords (er t) ws = pubWords t ws) ∧ (∀ j p, pubArm (er t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      have hs := sNo_er (.prod a b)
      simp only [er] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (er a) (er b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, wc_er, iha.1, ihb.1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have hs := sNo_er (.sum a b)
      have ht := tier_er (.sum a b)
      have hl := lnorm_er (.sum a b)
      simp only [er] at hs ht hl ⊢
      have hal : (armsOf (er a)).length = (armsOf a).length := by rw [armsOf_er, List.length_map]
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
      · simp only [pubArm, hal, iha.2, ihb.2]
  | refine t ψ ih =>
      exact ⟨fun ws => by simp only [er]; rw [pubWords_refine, pubWords_refine, ih.1],
        fun j p => by simp only [er, pubArm, ih.2]⟩
  | iall t ih =>
      have hs := sNo_er (.iall t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iex t ih =>
      have hs := sNo_er (.iex t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | mu t ih =>
      have hs := sNo_er (.mu t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | tex κ t ih =>
      have hs := sNo_er (.tex κ t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | array i e _ =>
      have hs := sNo_er (.array i e)
      simp only [er] at hs ⊢
      have h1 : ∀ ws, pubWords (.array i (er e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ =>
      exact ⟨fun ws => by simp only [er, pubWords, sNo]; rfl,
        fun j p => by simp only [er, pubArm, pubWords, sNo]; rfl⟩
  | ptrOpt μ u _ =>
      exact ⟨fun ws => by simp only [er, pubWords, sNo]; rfl,
        fun j p => by simp only [er, pubArm, pubWords, sNo]; rfl⟩
  | loc μ u _ =>
      exact ⟨fun ws => by simp only [er, pubWords, sNo]; rfl,
        fun j p => by simp only [er, pubArm, pubWords, sNo]; rfl⟩
  | code a b _ _ =>
      exact ⟨fun ws => by simp only [er, pubWords, sNo], fun j p => by simp only [er, pubArm, pubWords, sNo]⟩
  | _ => exact ⟨fun ws => by simp [er, pubWords, sNo], fun j p => by simp [er, pubArm, pubWords, sNo]⟩

/-- **Counted words depend only on the signature.** -/
theorem pubWords_sig {a b : Ty} (h : sig a = sig b) (ws : List Word) : pubWords a ws = pubWords b ws := by
  have ea : pubWords (sig a) ws = pubWords a ws := by
    simp only [sig]; rw [(pubWords_er _).1, (pubWords_skel a).1]
  have eb : pubWords (sig b) ws = pubWords b ws := by
    simp only [sig]; rw [(pubWords_er _).1, (pubWords_skel b).1]
  rw [← ea, ← eb, h]

/-! ## 2. The binding contract of a load -/

/-- A load's reads skip the reader's own promises: under `PromAbove` after the load (loads keep
memory and promises), every promise lies above the post-load coherence. -/
theorem readsR_of_pa {arch : Arch} {pw : Word} {ad : Address} {acq : Bool} {us : List Acc} {mem : Memory}
    {pairs : List Ts} {th : TTh} {r : St × List Word} (hr : r ∈ loadUnits arch pw ad acq us 0 (stOf mem pairs th))
    (hpa : PromAbove r.1) : TermK2aLoad.ReadsR mem pairs ad th.promises us 0 r.2 := by
  obtain ⟨s', ws⟩ := r
  obtain ⟨f1, -, f3, -⟩ := TermArch.loadUnits_frame arch pw ad acq us 0 (stOf mem pairs th) hr
  exact TermK2aLoad.loadUnits_readsR us 0 (stOf mem pairs th) (s', ws) hr th.promises
    (fun t m ht hm => hpa t (by rw [f3]; exact ht) m (by rw [f1]; exact hm))

/-- **A load's result is new-fine** (K-2a, loads): a load at a component `U` of a laid-out cell of
`sto`, its result bound at a runtime type `ru` of `U`'s signature. -/
theorem valB_load {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh} {arch : Arch} {pw : Word}
    {ad : Address} {acq : Bool} {us : List Acc} {c : Cell} {U ru : Ty} {ini : AllocLabel → Nat}
    (hsto : sto ad.label = some c) (hlt : LayT c.ty) (hat : AtOff c.ty ad.offset U) (hini : IniAt ini c ad U)
    (hU : ∀ N e, U ≠ .array (.lit N) e) (hus : accs U = some us) (hG : GranuleWP sto mem pairs th.promises)
    (hsig : sig ru = sig U) {r : St × List Word} (hr : r ∈ loadUnits arch pw ad acq us 0 (stOf mem pairs th))
    (hpa : PromAbove r.1) (ga : AllocLabel) (N : AllocLabel → Prop) :
    TermK2a.ValB sto (stOf mem pairs th) ga N th ru r.2 := by
  obtain ⟨b, o, S, L, hseg, hbo, hatS, hL, -⟩ := at_seg hlt hat hini hU
  have hR := readsR_of_pa hr hpa
  intro w hw
  rw [pubWords_sig hsig] at hw
  exact TermK2aLoad.valB_of_reads (s := stOf mem pairs th) hR hsto hseg hL hatS hus hbo hG ga N w hw

/-- **A loaded binding's labels are published** (K-2a, `ThLbl`): the value read is a value of the
pointee (`VR`, from the reader's `MemInv`), so its counted words name cells of the reader's frontier
or boxes (`labsIn_pubVR`), which `Eg` has.  Every read is covered, another thread's outstanding
promise included: no claim is made about unread messages. -/
theorem lbl_load {ρ : Nat → Nat} {η : TEnv} {u ru : Ty} {ws : List Word} {G : AllocLabel → Prop}
    (hc : Coh η) (hP : ∀ l f, η.pfr l = some f → G l) (hB : ∀ l B, η.box l = some B → G l)
    (hsig : sig ru = sig (TermClose.cl ρ η.wit 0 0 u)) (hv : VR ρ η u (shp ru) ws)
    (hwc : wc ru = some ws.length) (hval : Valid ru ws) :
    ∀ w ∈ pubWords ru ws, ∀ l, Names l w → G l := by
  have hv' : VR ρ (CE η) (TermClose.cl ρ η.wit 0 0 u) (shp ru) ws :=
    (VR_close hc ρ u [] 0 ρ ρ (shp ru) ws (fun _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))).1 hv
  have h := labsIn_pubVR (TermClose.cl ρ η.wit 0 0 u) ρ (CE η) ru ws (fun _ _ _ h => h) hP hB hsig hwc hval hv'
  intro w hw l hn
  obtain ⟨a', g0, hg, rfl⟩ := hn
  exact h w hw a' g0 hg

/-- `Lay` gives the word count and validity at the runtime type. -/
theorem wc_valid_of_lay {σs : List Ty} {t rt : Ty} {ws : List Word} (hL : Lay σs t rt ws) :
    wc rt = some ws.length ∧ Valid rt ws := by
  refine ⟨?_, hL.2.2.2.1⟩
  have h1 := hL.2.2.1
  cases hu : accs rt with
  | none => simp [wc, hu] at h1
  | some us => simp only [wc, hu, Option.map_some]; rw [hL.1 us hu]

/-! ## 3. The per-operation contracts (fixed API) -/

/-- A label is in `Gl` or named by a counted word of an old binding. -/
def LblNew (Gl : AllocLabel → Prop) (th : TTh) (l : AllocLabel) : Prop :=
  Gl l ∨ ∃ b ∈ TermK2a.Binds th, ∃ w0 ∈ pubWords b.2.1 b.2.2, Names l w0

/-- **A step's contract** (K-2a): the binding contract for (R) (`StepB`), and every new binding's
counted words name labels of `Gl` or of old bindings (for `ThLbl`; per binding, never memory-wide). -/
def StepOK (sto : Sto) (s : St) (a : AllocLabel) (N Gl : AllocLabel → Prop) (th th' : TTh) : Prop :=
  TermK2a.StepB sto s.mem s.pairs a N th th' ∧
    ∀ b ∈ TermK2a.Binds th', b ∈ TermK2a.Binds th ∨ ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w → LblNew Gl th l

/-- **A load step's contract**: the step binds one new value (the frame's other bindings and the
stack unchanged), new-fine for (R) (`ValB`), whose counted words name labels of `G`. -/
def LdOK (sto : Sto) (s : St) (a : AllocLabel) (N G : AllocLabel → Prop) (th th' : TTh) : Prop :=
  ∃ x rt ws, th'.env = (x, rt, ws) :: th.env ∧ th'.stack = th.stack ∧ TermK2a.ValB sto s a N th rt ws ∧
    ∀ w ∈ pubWords rt ws, ∀ l, Names l w → G l

theorem stepOK_of_ldOK {sto : Sto} {s : St} {a : AllocLabel} {N Gl : AllocLabel → Prop} {th th' : TTh}
    (h : LdOK sto s a N Gl th th') : StepOK sto s a N Gl th th' := by
  obtain ⟨x, rt, ws, he, hst, hv, hl⟩ := h
  refine ⟨TermK2a.stepB_let he hst hv, fun b hb => ?_⟩
  unfold TermK2a.Binds at hb
  rw [he, hst] at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_cons.1 hb with e | hb
    · subst e; exact .inr fun w hw l hn => .inl (hl w hw l hn)
    · exact .inl (TermK2a.mem_binds_env hb)
  · exact .inl (List.mem_append_right _ hb)

/-- **`ThLbl` after the step**, from `ThLbl` before (at `Eg'`) and the contract's label half. -/
theorem thLbl_of_stepOK {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th th' : TTh}
    {Eg' : GEnv} (hL : ThLbl Eg' th)
    (hB : StepOK sto s a N (fun l => Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none) th th') : ThLbl Eg' th' := by
  have hold : ∀ b ∈ TermK2a.Binds th, ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w →
      Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro b hb w hw l hn
    unfold TermK2a.Binds at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hL.1 _ _ _ hb w hw l hn
    · obtain ⟨f, hf, hbf⟩ := List.mem_flatMap.1 hb
      exact hL.2 f hf _ _ _ hbf w hw l hn
  have hall : ∀ b ∈ TermK2a.Binds th', ∀ w ∈ pubWords b.2.1 b.2.2, ∀ l, Names l w →
      Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro b hb w hw l hn
    rcases hB.2 b hb with hb0 | hnew
    · exact hold b hb0 w hw l hn
    · rcases hnew w hw l hn with h | ⟨b0, hb0, w0, hw0, hn0⟩
      · exact h
      · exact hold b0 hb0 w0 hw0 l hn0
  exact ⟨fun x rt ws hm => hall _ (TermK2a.mem_binds_env hm),
    fun f hf x rt ws hm => hall _ (TermK2a.mem_binds_stack hf hm)⟩

/-- `ThLbl` moves along `Eg ⊆ Eg'`. -/
theorem thLbl_mono {Eg Eg' : GEnv} {th : TTh} (hL : ThLbl Eg th)
    (p5 : ∀ l f, Eg.pfr l = some f → Eg'.pfr l = some f) (p6 : ∀ l B, Eg.box l = some B → Eg'.box l = some B) :
    ThLbl Eg' th := by
  have hm : ∀ l, (Eg.pfr l ≠ none ∨ Eg.box l ≠ none) → Eg'.pfr l ≠ none ∨ Eg'.box l ≠ none := by
    intro l h
    rcases h with h | h
    · obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 h
      exact .inl (by rw [p5 l f hf]; simp)
    · obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.1 h
      exact .inr (by rw [p6 l B hB]; simp)
  exact ⟨fun x rt ws hm0 w hw l hn => hm l (hL.1 x rt ws hm0 w hw l hn),
    fun f hf x rt ws hm0 w hw l hn => hm l (hL.2 f hf x rt ws hm0 w hw l hn)⟩

/-! ## 4. Per-operation load contracts -/

/-- **`load` through an own pointer.** -/
theorem ld_own {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  have hacr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
  obtain ⟨us, hus, -, hld, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2 hsig
    hacr
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl hpr0
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← (Fd_lay hcty).2.2.1, ← hacr]; exact hus
  have hU : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at hUa; simp [accs] at hUa
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := ⟨lab, 0⟩) hc1 (hLay _ _ hc1) (Fd_AtOff hcty hacc) (IniAt_of_ne (ini := η.rc) hna) hU hUa hG hsig hl
    hpr0 ga N

/-- **`load` through a locative into an own cell.** -/
theorem ld_loc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hacr : accs ru = accs (cl ρ η.wit 0 0 u) :=
    accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2
  obtain ⟨us, hus, -, hld, -⟩ := locLoad (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2 hacr
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl' hpr0
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hacr]; exact hus
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load hc1 (hLay _ _ hc1) hat hini hna hUa hG hsig hl' hpr0 ga N

/-- **`load` through a pub pointer.** -/
theorem ld_pub {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hnwc : wordOf (close th.σs (.ptr .pub u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, -, hld, -⟩ :=
    loadPub_core (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk (bind_opaqueOK hb) hi hE htv hm
  obtain ⟨lab2, c, pw2, ru2, f, hea2, hpw2, hsto, hcty, -, -, hacc, -, hsig⟩ :=
    pubPtr_view hi hpk htv (bind_opaqueOK hb)
  rw [hea] at hea2
  simp only [Option.some.injEq, Prod.mk.injEq, Ty.ptr.injEq, true_and, List.cons.injEq, and_true] at hea2
  obtain ⟨rfl, rfl⟩ := hea2
  rw [hpw] at hpw2
  simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq, and_true] at hpw2
  subst hpw2
  have hwr : wordOf (Ty.ptr .pub ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have hacr : accs ru = accs (cl ρ η.wit 0 0 u) :=
    pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, -⟩ := hld s' wsr hl hpr0
  have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hacr]; exact hus
  have hU : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at hUa; simp [accs] at hUa
  have hc1 := hsto1 _ _ hsto
  obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
  refine ⟨x, ru, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
  exact valB_load (ad := ⟨lab, 0⟩) hc1 (hLay _ _ hc1) (Fd_AtOff hcty hacc) (IniAt_of_ne (ini := η.rc) hna) hU hUa
    hG hsig hl hpr0 ga N

/-- **`load` through a pub locative** (the thread's own cell, or another thread's). -/
theorem ld_pubLoc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {sto : Sto} (hsto1 : ∀ l c, η.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises) {Gl : AllocLabel → Prop}
    (hPf : ∀ l f, η.pfr l = some f → Gl l) (hBx : ∀ l B, η.box l = some B → Gl l)
    (ga : AllocLabel) (N : AllocLabel → Prop) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_target (rfl : cellOf (.loc .pub u) = some (.pub, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hlr := pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
  have hc1 := hsto1 _ _ hsto
  -- the common finish, from the loaded value's `VR` and `Lay`
  have fin : ∀ us, accs ru = some us →
      (∀ s' wsr, (s', wsr) ∈ loadUnits g.arch pw ad acq us 0 (stOf mem pairs th) → PromAbove s' →
        VR ρ η u (shp ru) wsr ∧ Lay th.σs u ru wsr) →
      ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
        LdOK sto (stOf mem pairs th) ga N Gl th r.2.2 := by
    intro us hus hld
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key]
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay⟩ := hld s' wsr hl' hpr0
    have hUa : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr]; exact hus
    obtain ⟨hwc, hval⟩ := wc_valid_of_lay hlay
    refine ⟨x, ru, wsr, rfl, rfl, ?_, lbl_load hE.2.1 hPf hBx hsig hvr hwc hval⟩
    exact valB_load hc1 (hLay _ _ hc1) hat hini hna hUa hG hsig hl' hpr0 ga N
  by_cases hown : c.owner = some η.tid
  · obtain ⟨us, hus, -, hld, -⟩ := locLoadI (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun _ f hf hns => by
        simp only [ModeOK] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        rcases hsf with hs | hs
        · exact absurd hs hns
        · exact hs pw (by simp)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtW hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    exact fin us hus fun s' wsr hl' hpa => by
      obtain ⟨hvr, hlay, -⟩ := hld (s', wsr) hl' hpa
      exact ⟨hvr, hlay⟩
  · simp only [ModeOK] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · exact hs pw (by simp)
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    obtain ⟨-, hval, -⟩ := pubLoadAt (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    refine fin us hus fun s' wsr hl' hpr0 => ?_
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us :=
      (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨hvr0, hV0⟩ := ValOf.env hq
    have hvr : VR ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_close hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_up _ _ q wsr hle hvr0)
    exact ⟨hvr, ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
      Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩⟩

end TermK2aLd
