import WeakCore.TermPtrRts
import WeakCore.TermInterf
import WeakCore.TermPlantF

/-!
# TermPtrStab: stability of `tminG` across steps (for the T1–T3)

* `tminG_thread` (T1+T2, thread step of `i`): every thread's `tminG` is unchanged, given that the
  stepper keeps its old `tmin` (K-3) and has no outstanding promise at one of its fresh labels
  (`PromAllocF`'s location half).
* `tminG_prom_fgn` (T2, promise of `j`): other threads' `tminG` is unchanged.
* `tminG_prom_own_some` (T3a): the promiser's `tminG`, once some, is unchanged.
* `tminG_plant` (T3b): at the promise planting `l`, `tminG = some c.mem.size`, given the
  invariant `NoEdgeUnpl` (no owner promise is a plant edge to an unplanted own cell).
-/

namespace TermPtrStab
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermCut TermSys TermMain TermPtrRts
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## List-level stability of `tminOf` -/

/-- Edges agree where the message agrees and the store typing agrees at its cell. -/
theorem edgeB_agree {sto sto2 : Sto} {s s2 : St} {a : AllocLabel} {u : Ts} {m : Msg}
    (hm1 : s.mem[u]? = some m) (hm2 : s2.mem[u]? = some m) (hl : sto2 m.loc.label = sto m.loc.label) :
    edgeB sto2 s2 a u = edgeB sto s a u := by
  apply Bool.eq_iff_iff.2
  rw [edgeB_iff, edgeB_iff, hm1, hm2]
  constructor
  · rintro ⟨m1, h1, ⟨ca, e1, e2, e3⟩, e4⟩
    cases h1
    exact ⟨m, rfl, ⟨ca, hl ▸ e1, e2, e3⟩, e4⟩
  · rintro ⟨m1, h1, ⟨ca, e1, e2, e3⟩, e4⟩
    cases h1
    exact ⟨m, rfl, ⟨ca, hl.symm ▸ e1, e2, e3⟩, e4⟩

/-- Shrinking the promises, edges kept on the survivors, the old `tmin` surviving: `tmin` kept. -/
theorem tminOf_shrink {sto sto2 : Sto} {s s2 : St} {a : AllocLabel}
    (hp : ∀ u ∈ s2.promises, u ∈ s.promises)
    (he : ∀ u ∈ s2.promises, edgeB sto2 s2 a u = edgeB sto s a u)
    (hk : ∀ t, tminOf sto s a = some t → t ∈ s2.promises) :
    tminOf sto2 s2 a = tminOf sto s a := by
  have hsub : ∀ x, x ∈ s2.promises.filter (edgeB sto2 s2 a) → x ∈ s.promises.filter (edgeB sto s a) := by
    intro x hx
    rw [List.mem_filter] at hx ⊢
    exact ⟨hp x hx.1, (he x hx.1) ▸ hx.2⟩
  cases h : tminOf sto s a with
  | none =>
    have h0 : s.promises.filter (edgeB sto s a) = [] := List.min?_eq_none_iff.1 h
    have h1 : s2.promises.filter (edgeB sto2 s2 a) = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun x hx => by
        have := hsub x hx
        rw [h0] at this; cases this
    unfold tminOf
    rw [h1]; rfl
  | some t =>
    have ht := hk t h
    have hmin := List.min?_eq_some_iff.1 h
    unfold tminOf
    apply List.min?_eq_some_iff.2
    refine ⟨?_, fun b hb => hmin.2 b (hsub b hb)⟩
    rw [List.mem_filter]
    refine ⟨ht, ?_⟩
    rw [he t ht]
    exact (List.mem_filter.1 hmin.1).2

/-- Appending a later promise, edges kept on the old ones: a `tmin` is kept. -/
theorem tminOf_grow {sto sto2 : Sto} {s s2 : St} {a : AllocLabel} {n t : Ts}
    (hp : s2.promises = s.promises ++ [n]) (hlt : ∀ u ∈ s.promises, u < n)
    (he : ∀ u ∈ s.promises, edgeB sto2 s2 a u = edgeB sto s a u)
    (h : tminOf sto s a = some t) : tminOf sto2 s2 a = some t := by
  have hmin := List.min?_eq_some_iff.1 h
  have ht := List.mem_filter.1 hmin.1
  unfold tminOf
  apply List.min?_eq_some_iff.2
  rw [hp, List.filter_append]
  refine ⟨List.mem_append_left _ (List.mem_filter.2 ⟨ht.1, (he t ht.1).symm ▸ ht.2⟩), ?_⟩
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · have hb1 := List.mem_filter.1 hb
    exact hmin.2 b (List.mem_filter.2 ⟨hb1.1, (he b hb1.1) ▸ hb1.2⟩)
  · have hb1 := (List.mem_filter.1 hb).1
    rw [List.mem_singleton] at hb1
    subst hb1
    exact Nat.le_of_lt (hlt t ht.1)

/-- Appending a later promise that is an edge, with no old edge: `tmin` is the new promise. -/
theorem tminOf_grow_none {sto sto2 : Sto} {s s2 : St} {a : AllocLabel} {n : Ts}
    (hp : s2.promises = s.promises ++ [n])
    (he : ∀ u ∈ s.promises, edgeB sto2 s2 a u = edgeB sto s a u)
    (h : tminOf sto s a = none) (hn : edgeB sto2 s2 a n = true) : tminOf sto2 s2 a = some n := by
  have h0 : s.promises.filter (edgeB sto s a) = [] := List.min?_eq_none_iff.1 h
  have h1 : s.promises.filter (edgeB sto2 s2 a) = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun x hx => by
      have hx1 := List.mem_filter.1 hx
      have : x ∈ s.promises.filter (edgeB sto s a) := List.mem_filter.2 ⟨hx1.1, (he x hx1.1) ▸ hx1.2⟩
      rw [h0] at this; cases this
  unfold tminOf
  rw [hp, List.filter_append, h1, List.nil_append, List.filter_cons_of_pos hn, List.filter_nil]
  rfl

/-! ## Configuration-level stability -/

theorem push_get {mem : Memory} {x : Msg} {u : Ts} (h : u < mem.size) : (mem.push x)[u]? = mem[u]? := by
  rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

theorem EgT_sto_old {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {c' : Cfg} {l : AllocLabel}
    (h : ¬ FreshIn g n n' l) : (EgT Eg g n n' E' c').sto l = Eg.sto l := post_sto_old h

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **T1 + T2 (thread step of `i`)**: every thread's `tminG` is unchanged at `EgT`, given that
the stepper keeps its old `tmin` (`hkeep`, K-3) and has no outstanding promise at one of the
step's fresh labels (`hfr`, `PromAllocF`'s location half). -/
theorem tminG_thread {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (E' : TEnv)
    (hfr : ∀ u ∈ r.2.2.promises, ∀ m, r.1[u]? = some m →
      ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label)
    (hkeep : ∀ t, tminG Eg c i l = some t → t ∈ r.2.2.promises) (j : Nat) :
    tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j l = tminG Eg c j l := by
  have hext : ∀ (u : Ts) (m : Msg), c.mem[u]? = some m → r.1[u]? = some m :=
    (TermCert.tstep_appUp X.hr).2.1
  have hget : ∀ (q : Nat) (thq : TTh) (u : Ts), c.ths[q]? = some thq → u ∈ thq.promises →
      ∃ m, c.mem[u]? = some m ∧ r.1[u]? = some m := by
    intro q thq u hq hu
    have hlt := X.inv.plt q thq u hq hu
    refine ⟨c.mem[u], (Array.getElem?_eq_getElem hlt), hext u _ (Array.getElem?_eq_getElem hlt)⟩
  by_cases hji : j = i
  · subst hji
    rw [tminG_eq X.e3, tminG_eq X.hth, X.e1]
    rw [tminG_eq X.hth] at hkeep
    refine tminOf_shrink (fun u hu => TermInterf.tctx_sub X u hu) (fun u hu => ?_) hkeep
    obtain ⟨m, hm1, hm2⟩ := hget j th u X.hth (TermInterf.tctx_sub X u hu)
    exact edgeB_agree hm1 hm2 (EgT_sto_old (hfr u hu m hm2))
  · have hthj := X.ho j hji
    cases hq : c.ths[j]? with
    | none =>
      unfold tminG
      rw [hthj, hq]
    | some thj =>
      rw [tminG_eq (hthj.trans hq), tminG_eq hq, X.e1]
      refine tminOf_shrink (fun u hu => hu) (fun u hu => ?_) (fun t ht => (tminOf_spec ht).1)
      obtain ⟨m, hm1, hm2⟩ := hget j thj u hq hu
      refine edgeB_agree hm1 hm2 (EgT_sto_old ?_)
      rintro ⟨q, hq1, -, hl⟩
      have hin := (X.inv.fresh i th X.hth q hq1).2.2.2.2 u m hm1 hl
      exact X.inv.disj j i thj th u hji hq X.hth hu hin

/-- **T2 (thread step of `i`, foreign owner `j ≠ i`)**: no `hkeep` needed. -/
theorem tminG_thread_fgn {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (E' : TEnv) {j : Nat} (hji : j ≠ i) :
    tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j l = tminG Eg c j l := by
  have hext : ∀ (u : Ts) (m : Msg), c.mem[u]? = some m → r.1[u]? = some m :=
    (TermCert.tstep_appUp X.hr).2.1
  have hthj := X.ho j hji
  cases hq : c.ths[j]? with
  | none =>
    unfold tminG
    rw [hthj, hq]
  | some thj =>
    rw [tminG_eq (hthj.trans hq), tminG_eq hq, X.e1]
    refine tminOf_shrink (fun u hu => hu) (fun u hu => ?_) (fun t ht => (tminOf_spec ht).1)
    have hlt := X.inv.plt j thj u hq hu
    have hm1 : c.mem[u]? = some c.mem[u] := Array.getElem?_eq_getElem hlt
    refine edgeB_agree hm1 (hext u _ hm1) (EgT_sto_old ?_)
    rintro ⟨q, hq1, -, hl⟩
    have hin := (X.inv.fresh i th X.hth q hq1).2.2.2.2 u _ hm1 hl
    exact X.inv.disj j i thj th u hji hq X.hth hu hin

/-- **T2 (promise of `j`)**: the other threads' `tminG` is unchanged at `EgP`. -/
theorem tminG_prom_fgn {c : Cfg} {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    {j n q : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel}
    (hth : c.ths[j]? = some th) (hplt : AllPromLt c) (hqj : q ≠ j) :
    tminG (EgP Eg P N j n) (promise c j a v w) q l = tminG Eg c q l := by
  have e := (promise_inv (a := a) (v := v) (w := w) hth).1
  cases hq : c.ths[q]? with
  | none =>
    unfold tminG
    rw [promise_other hqj, hq]
  | some thq =>
    rw [tminG_eq ((promise_other hqj).trans hq), tminG_eq hq]
    refine tminOf_congr rfl rfl fun u hu => ?_
    rw [e]
    exact push_get (hplt q thq u hq hu)

/-- **T3a (promise of the owner)**: a `tminG` that is some is unchanged at `EgP`. -/
theorem tminG_prom_own_some {c : Cfg} {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} {t : Ts}
    (hth : c.ths[j]? = some th) (hplt : AllPromLt c) (ht : tminG Eg c j l = some t) :
    tminG (EgP Eg P N j n) (promise c j a v w) j l = some t := by
  have hi := promise_inv (a := a) (v := v) (w := w) hth
  rw [tminG_eq hi.2.1, hi.2.2]
  rw [tminG_eq hth] at ht
  refine tminOf_grow rfl (fun u hu => hplt j th u hth hu) (fun u hu => ?_) ht
  exact edgeB_congr rfl (push_get (hplt j th u hth hu))

/-- No outstanding promise of an owner is a plant edge (at `Eg.sto`) to one of its unplanted
cells. -/
def NoEdgeUnpl (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (l : AllocLabel) (cl : Cell), Eg.sto l = some cl → cl.owner = some j → Eg.pfr l = none →
    tminG Eg c j l = none

/-- **T3b (the planting promise)**: under `NoEdgeUnpl`, the promise of `j` planting `l` is the
only plant edge to `l`, so `tminG = some c.mem.size`. -/
theorem tminG_plant {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} {cl : Cell} {f : Ts}
    (hNE : NoEdgeUnpl Eg c) (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c)
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some j) (hpf : Eg.pfr l = none)
    (hpl : P l = some f) :
    tminG (EgP Eg P N j n) (promise c j a v w) j l = some c.mem.size := by
  have hi := promise_inv (a := a) (v := v) (w := w) hth
  have h0 := hNE j l cl hsto hown hpf
  rw [tminG_eq hth] at h0
  rw [tminG_eq hi.2.1, hi.2.2]
  have he : ∀ u ∈ th.promises, edgeB Eg.sto (promSt (stOf c.mem c.pairs th) a v w) l u =
      edgeB Eg.sto (stOf c.mem c.pairs th) l u :=
    fun u hu => edgeB_congr rfl (push_get (hplt j th u hth hu))
  refine tminOf_grow_none rfl he h0 ?_
  obtain ⟨hL, -⟩ := hPL _ _ hpl
  obtain ⟨l', -, u, hu, m, hm, hml, ⟨ca, hca, hno, hrf⟩, a', g, hv, ha', -⟩ := hL
  have hE : PlantEdge Eg.sto m l :=
    ⟨⟨ca, hml ▸ cut_sto_le Eg j (fun _ => False) _ _ hca, hno, hrf⟩, a', g, hv, ha'⟩
  rcases List.mem_append.1 hu with hu | hu
  · exfalso
    have hm0 : c.mem[u]? = some m := by
      rw [← push_get (hplt j th u hth hu)]; exact hm
    exact tminOf_none h0 u hu m hm0 hE
  · rw [List.mem_singleton] at hu
    subst hu
    apply edgeB_iff.2
    exact ⟨m, hm, hE⟩

/-! ## `NoEdgeUnpl` from `promClos` and `PromInCut` -/

theorem promInCut_init {Eg : GEnv} {c : Cfg} (h : AllNoProm c) : PromInCut Eg c := by
  intro j th t m hj ht
  rw [h j th hj] at ht; cases ht

/-- **`NoEdgeUnpl`** from the `SysInvN` clause `promClos` and `PromInCut` (hk-free). -/
theorem noEdgeUnpl_of {Eg : GEnv} {c : Cfg} (hC : PromClosG Eg c) (hI : PromInCut Eg c) : NoEdgeUnpl Eg c := by
  intro j l cl hsto hown hpf
  cases hq : c.ths[j]? with
  | none => unfold tminG; rw [hq]
  | some th =>
    rw [tminG_eq hq]
    cases ht : tminOf Eg.sto (stOf c.mem c.pairs th) l with
    | none => rfl
    | some t =>
      exfalso
      obtain ⟨htp, m, hm, ⟨ca, hca, hno, hrf⟩, a', g, hv, ha'⟩ := tminOf_spec ht
      have hsa : Eg.sto a'.label = some cl := by rw [ha']; exact hsto
      obtain ⟨f, hf⟩ := hC j th t m hq htp hm a' g hv cl hsa hown ca hca (hI j th t m hq htp hm ca hca) hno hrf
      rw [ha', hpf] at hf; cases hf

/-- `PromInCut` across a thread step of `i` (given the global footprint, `TermInterf.gfoot_of`). -/
theorem promInCut_thread {c c' : Cfg} {Eg Eg2 : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {v : Ts}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hG : GFoot (gOf p k arch c i) Eg Eg2 th.nalloc r.2.2.nalloc v) (h : PromInCut Eg c) : PromInCut Eg2 c' := by
  intro j thj t m hj ht hm cm hcm
  obtain ⟨th0, h0, hs0, -, hne⟩ := TermInterf.tctx_old X hj
  have ht0 := hs0 t ht
  have hlt := X.inv.plt j th0 t h0 ht0
  have hm0 : c.mem[t]? = some m := by
    have hm1 : c.mem[t]? = some c.mem[t] := Array.getElem?_eq_getElem hlt
    have h2 : r.1[t]? = some c.mem[t] := (TermCert.tstep_appUp X.hr).2.1 t _ hm1
    rw [← X.e1, hm] at h2; cases h2; exact hm1
  rcases hG.2.1 m.loc.label with e | ⟨hf, -, -, T, e⟩
  · rw [e] at hcm
    rcases h j th0 t m h0 ht0 hm0 cm hcm with ho | ⟨f, hf⟩
    · exact .inl ho
    · refine .inr ⟨f, ?_⟩
      rcases hG.2.2.2.2.1 m.loc.label with e2 | ⟨e2, -⟩ | ⟨-, e2, -⟩
      · rw [e2]; exact hf
      · rw [hf] at e2; cases e2
      · rw [hf] at e2; cases e2
  · rw [e] at hcm; cases hcm
    by_cases hji : j = i
    · subst hji; exact .inl rfl
    · exfalso
      obtain ⟨q, hq1, -, hl⟩ := hf
      have hin := (X.inv.fresh i th X.hth q hq1).2.2.2.2 t m hm0 hl
      exact X.inv.disj j i th0 th t hji h0 X.hth ht0 hin

/-- `PromInCut` across a thread step of `i`, at `SysInvN`'s post environment `EgT` (the wiring form). -/
theorem promInCut_threadT {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i)
      (db i) δ)
    (h : PromInCut Eg c) : PromInCut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  have h2 := promInCut_thread X (TermInterf.gfoot_of X Y Z) h
  exact h2

/-- `PromInCut` across a promise step of `j` (given `PromLocF`'s conclusion `hloc`). -/
theorem promInCut_prom {c : Cfg} {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hplt : AllPromLt c)
    (hfr : ∀ q, th.nalloc ≤ q → Eg.sto (freshLabel c.lbase c.n j q) = none)
    (hloc : (∃ cl, cutSto Eg j a.label = some cl) ∨ ∃ q, th.nalloc ≤ q ∧ a.label = freshLabel c.lbase c.n j q)
    (h : PromInCut Eg c) : PromInCut (EgP Eg P N j n) (promise c j a v w) := by
  have hi := promise_inv (a := a) (v := v) (w := w) hth
  have hsh : ∀ l, Eg.Shared l → (EgP Eg P N j n).Shared l := by
    intro l ⟨f, hf⟩
    show ∃ f, (match P l with | some f => some f | none => Eg.pfr l) = some f
    cases P l with
    | some f2 => exact ⟨f2, rfl⟩
    | none => exact ⟨f, hf⟩
  intro q thq t m hq ht hm cm hcm
  have hcm0 : Eg.sto m.loc.label = some cm := hcm
  have hmem : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by rw [hi.1]
  by_cases hqj : q = j
  · subst hqj
    rw [hi.2.1] at hq; cases hq
    rcases List.mem_append.1 ht with ht | ht
    · have hlt := hplt q th t hth ht
      rw [hmem, push_get hlt] at hm
      rcases h q th t m hth ht hm cm hcm0 with ho | hs
      · exact .inl ho
      · exact .inr (hsh _ hs)
    · rw [List.mem_singleton] at ht
      subst ht
      rw [hmem, Array.getElem?_push_size] at hm
      cases hm
      rcases hloc with ⟨cl, hcl⟩ | ⟨q2, hq2, hl⟩
      · obtain ⟨e1, ho⟩ := cutSto_some.1 hcl
        rw [hcm0] at e1; cases e1
        rcases ho with ho | hs
        · exact .inl ho
        · exact .inr (hsh _ hs)
      · exfalso
        have := hfr q2 hq2
        dsimp only at hcm0
        rw [hl, this] at hcm0; cases hcm0
  · rw [promise_other hqj] at hq
    have hlt := hplt q thq t hq ht
    rw [hmem, push_get hlt] at hm
    rcases h q thq t m hq ht hm cm hcm0 with ho | hs
    · exact .inl ho
    · exact .inr (hsh _ hs)

end

/-! ## (PtrRtsPost) `PtrRtsG` across a promise step -/


/-- A plant edge carried by a message that is no thread's promise names a planted/published cell or
a box (proved from `MemOKP`: `nonPromLbl_of`). -/
def NonPromLbl (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (u : Ts) (m : Msg) (L : AllocLabel), c.mem[u]? = some m → PlantEdge Eg.sto m L →
    (∀ (q : Nat) (thq : TTh), c.ths[q]? = some thq → u ∉ thq.promises) → Eg.pfr L ≠ none ∨ Eg.box L ≠ none

theorem push_get_ne {mem : Memory} {x : Msg} {u : Ts} {m : Msg} (h : (mem.push x)[u]? = some m)
    (hne : u ≠ mem.size) : mem[u]? = some m := by
  rw [Array.getElem?_push] at h
  simp only [hne, ite_false] at h
  exact h

theorem promise_mem {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by
  rw [(promise_inv (a := a) (v := v) (w := w) hth).1]

theorem egP_pfr_none {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    {l : AllocLabel} (h : P l = none) : (EgP Eg P N j n).pfr l = Eg.pfr l := by
  simp [EgP, GEnv.withFp, plantG, h]

/-- A planted label is an unplanted cell of the promiser. -/
theorem plantOf_target {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {L : AllocLabel} {f : Ts} (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hP : P L = some f) :
    ∃ cl, Eg.sto L = some cl ∧ cl.owner = some j ∧ Eg.pfr L = none := by
  obtain ⟨hPL, -⟩ := hPL _ _ hP
  obtain ⟨l', -, u, -, m, -, -, -, a', g, -, rfl, cl, hcl, ho, hpn⟩ := hPL
  exact ⟨cl, cut_sto_le Eg j _ _ _ hcl, ho, hpn⟩

theorem box_none_of_sto {Eg : GEnv} (hBS : TermBoxZ.BoxSto Eg) {L : AllocLabel} {cl : Cell}
    (hs : Eg.sto L = some cl) : Eg.box L = none := by
  cases hb : Eg.box L with
  | none => rfl
  | some B => rw [hBS L B hb] at hs; cases hs

/-- `PtrRtsG` after the promise, at the promiser `j`. -/
theorem ptrRtsG_prom_own {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c) (hG : PtrRtsG Eg Tot HP c) (hL : LblSto Eg c)
    (hT : GateTmin Eg Tot HP c) (hNE : NoEdgeUnpl Eg c) (hFP : FgnPromClosG Eg c) (hNP : NonPromLbl Eg c)
    (hBS : TermBoxZ.BoxSto Eg) {L : AllocLabel} {cl : Cell} {f : Ts}
    (hsto : Eg.sto L = some cl) (hown : cl.owner = some j)
    (hpf : (EgP Eg P N j n).pfr L = some f)
    (hk0 : 0 < (Tot j + HP j) (.own L)) (t : Ts)
    (ht : tminG (EgP Eg P N j n) (promise c j a v w) j L = some t) :
    MemRts Eg.sto t L (promise c j a v w).mem (th.promises ++ [c.mem.size]) ∧
      ThRts t L { th with promises := th.promises ++ [c.mem.size] } := by
  rw [promise_mem hth]
  cases hP : P L with
  | none =>
    have hpf0 : Eg.pfr L = some f := by rw [egP_pfr_none hP] at hpf; exact hpf
    obtain ⟨t0, ht0⟩ := Option.ne_none_iff_exists'.1 (hT j L cl f hsto hown hpf0 hk0)
    rw [tminG_prom_own_some (a := a) (v := v) (w := w) hth hplt ht0] at ht
    have e0 := Option.some.inj ht
    subst e0
    obtain ⟨hM, hR⟩ := hG j th L cl f hth hsto hown hpf0 hk0 t0 ht0
    refine ⟨fun u m hu hE hnp => ?_, hR⟩
    have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
    exact hM u m (push_get_ne hu hne) hE (fun h => hnp (List.mem_append_left _ h))
  | some f' =>
    obtain ⟨cl', hcl', -, hpn0⟩ := plantOf_target hPL hP
    rw [tminG_plant hNE hth hPL hplt hsto hown hpn0 hP] at ht
    cases ht
    have hbox := box_none_of_sto hBS hsto
    refine ⟨fun u m hu hE hnp => ?_, ?_⟩
    · exfalso
      have hne : u ≠ c.mem.size := fun h => hnp (List.mem_append_right _ (List.mem_singleton.2 h))
      have hmu := push_get_ne hu hne
      by_cases hpr : ∃ (q : Nat) (thq : TTh), c.ths[q]? = some thq ∧ u ∈ thq.promises
      · obtain ⟨q, thq, hq, hu'⟩ := hpr
        obtain ⟨⟨cm, hcm, hno, hrf⟩, a', g, hv, ha'⟩ := hE
        rcases hFP q thq u m hq hu' hmu a' g hv cm hcm hno hrf with
          ⟨f2, hf2⟩ | ⟨cl2, hcl2, ho2⟩ | ⟨B, hB⟩ | ⟨n2, -, hn2⟩
        · rw [ha', hpn0] at hf2; cases hf2
        · rw [ha', hsto] at hcl2
          cases hcl2
          rw [hown] at ho2
          cases ho2
          rw [hth] at hq
          cases hq
          exact hnp (List.mem_append_left _ hu')
        · rw [ha', hbox] at hB; cases hB
        · rw [ha', hsto] at hn2; cases hn2
      · rcases hNP u m L hmu hE (fun q thq h1 h2 => hpr ⟨q, thq, h1, h2⟩) with h1 | h1
        · exact h1 hpn0
        · exact h1 hbox
    · obtain ⟨he, hst⟩ := hL j th hth
      exact ⟨envRts_of_unnamed he hpn0 hbox _, fun f hf => envRts_of_unnamed (hst f hf) hpn0 hbox _⟩

/-- `PtrRtsG` after the promise of `j`, at another owner `q`. -/
theorem ptrRtsG_prom_fgn {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {N : AllocLabel → Nat}
    {j n q : Nat} {th thq : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c) (hG : PtrRtsG Eg Tot HP c) (hqj : q ≠ j)
    (hq : c.ths[q]? = some thq) {L : AllocLabel} {cl : Cell} {f : Ts}
    (hsto : Eg.sto L = some cl) (hown : cl.owner = some q)
    (hpf : (EgP Eg P N j n).pfr L = some f)
    (hk0 : 0 < (Tot q + HP q) (.own L)) (t : Ts)
    (ht : tminG (EgP Eg P N j n) (promise c j a v w) q L = some t) :
    MemRts Eg.sto t L (promise c j a v w).mem thq.promises ∧ ThRts t L thq := by
  rw [promise_mem hth]
  rw [tminG_prom_fgn hth hplt hqj] at ht
  have hpf0 : Eg.pfr L = some f := by
    cases hP : P L with
    | none => rw [egP_pfr_none hP] at hpf; exact hpf
    | some f' =>
      obtain ⟨cl', hcl', ho', -⟩ := plantOf_target hPL hP
      rw [hsto] at hcl'
      cases hcl'
      rw [hown] at ho'
      cases ho'
      exact absurd rfl hqj
  obtain ⟨hM, hR⟩ := hG q thq L cl f hq hsto hown hpf0 hk0 t ht
  refine ⟨fun u m hu hE hnp => ?_, hR⟩
  by_cases hun : u = c.mem.size
  · rw [hun]
    rw [tminG_eq hq] at ht
    exact Nat.le_of_lt (hplt q thq t hq (tminOf_spec ht).1)
  · exact hM u m (push_get_ne hu hun) hE hnp

/-- **PtrRtsPost**: `PtrRtsG` across a promise of `j`, at the planted environment `EgP`, for any
holdings `HP2` with no own key gained (`ownKey_noIncrease_prom_noHS`). -/
theorem ptrRtsG_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP HP2 : Nat → Res} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c) (hG : PtrRtsGL Eg Tot HP c)
    (hkey : ∀ q l, (Tot q + HP2 q) (.own l) ≤ (Tot q + HP q) (.own l))
    (hNE : NoEdgeUnpl Eg c) (hFP : FgnPromClosG Eg c) (hNP : NonPromLbl Eg c) (hBS : TermBoxZ.BoxSto Eg) :
    PtrRtsG (EgP Eg P N j n) Tot HP2 (promise c j a v w) := by
  intro q thq L cl f hq hsto hown hpf hk t ht
  have hk0 : 0 < (Tot q + HP q) (.own L) := Nat.lt_of_lt_of_le hk (hkey q L)
  by_cases hqj : q = j
  · rw [hqj] at hq hown hk0 ht
    rw [(promise_inv (a := a) (v := v) (w := w) hth).2.1] at hq
    cases hq
    exact ptrRtsG_prom_own hth hPL hplt hG.1 hG.2.1 hG.2.2.1 hNE hFP hNP hBS hsto hown hpf hk0 t ht
  · have hq0 : c.ths[q]? = some thq := (promise_other hqj).symm.trans hq
    exact ptrRtsG_prom_fgn hth hPL hplt hG.1 hqj hq0 hsto hown hpf hk0 t ht


theorem egP_pfr_keep {P : AllocLabel → Option Ts} {Eg : GEnv} {c : Cfg} {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    {N : AllocLabel → Nat} (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) {l : AllocLabel} {f : Ts} (h : Eg.pfr l = some f) :
    (EgP Eg P N j n).pfr l = some f := by
  cases hP : P l with
  | none => rw [egP_pfr_none hP]; exact h
  | some f' =>
    obtain ⟨-, -, -, hpn⟩ := plantOf_target hPL hP
    rw [hpn] at h; cases h

/-- `LblSto` across a promise: frames are unchanged, frontiers only planted from none, boxes kept. -/
theorem lblSto_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {N : AllocLabel → Nat} {j n : Nat} {th : TTh} {a : Address}
    {v : WeakMem.Val} {w : Ts} (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hL : LblSto Eg c) :
    LblSto (EgP Eg P N j n) (promise c j a v w) := by
  have hp : ∀ l f, Eg.pfr l = some f → (EgP Eg P N j n).pfr l = some f :=
    fun l f h => egP_pfr_keep hPL h
  have hb : ∀ l B, Eg.box l = some B → (EgP Eg P N j n).box l = some B :=
    fun l B h => h
  intro i thi hi
  by_cases hij : i = j
  · rw [hij, (promise_inv (a := a) (v := v) (w := w) hth).2.1] at hi
    cases hi
    obtain ⟨he, hst⟩ := hL j th hth
    exact ⟨envLbl_mono hp hb he, fun f hf => envLbl_mono hp hb (hst f hf)⟩
  · rw [promise_other hij] at hi
    obtain ⟨he, hst⟩ := hL i thi hi
    exact ⟨envLbl_mono hp hb he, fun f hf => envLbl_mono hp hb (hst f hf)⟩

/-- `GateTmin` across a promise ((b)): a planted label gets `tminG = some c.mem.size`
(`tminG_plant`); a label with an old frontier keeps its `tminG` (`tminG_prom_own_some`/`_fgn`), its
gate holding before (no own key gained, `hkey`). -/
theorem gateTmin_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP HP2 : Nat → Res} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c) (hT : GateTmin Eg Tot HP c)
    (hkey : ∀ q l, (Tot q + HP2 q) (.own l) ≤ (Tot q + HP q) (.own l)) (hNE : NoEdgeUnpl Eg c) :
    GateTmin (EgP Eg P N j n) Tot HP2 (promise c j a v w) := by
  intro q L cl f hsto hown hpf hk
  have hsto0 : Eg.sto L = some cl := hsto
  have hk0 : 0 < (Tot q + HP q) (.own L) := Nat.lt_of_lt_of_le hk (hkey q L)
  cases hP : P L with
  | none =>
    have hpf0 : Eg.pfr L = some f := by rw [egP_pfr_none hP] at hpf; exact hpf
    obtain ⟨t0, ht0⟩ := Option.ne_none_iff_exists'.1 (hT q L cl f hsto hown hpf0 hk0)
    by_cases hqj : q = j
    · rw [hqj] at ht0 ⊢
      rw [tminG_prom_own_some (a := a) (v := v) (w := w) hth hplt ht0]
      exact fun h => by cases h
    · rw [tminG_prom_fgn hth hplt hqj, ht0]
      exact fun h => by cases h
  | some f' =>
    obtain ⟨cl', hcl', ho', hpn0⟩ := plantOf_target hPL hP
    rw [hsto0] at hcl'
    cases hcl'
    rw [hown] at ho'
    cases ho'
    rw [tminG_plant hNE hth hPL hplt hsto0 hown hpn0 hP]
    exact fun h => by cases h

/-- **PtrRtsPost, staging package**: `PtrRtsGL` across a promise of `j`. -/
theorem ptrRtsGL_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP HP2 : Nat → Res} {N : AllocLabel → Nat}
    {j n : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j th a v w l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l0) (hplt : AllPromLt c) (hG : PtrRtsGL Eg Tot HP c)
    (hkey : ∀ q l, (Tot q + HP2 q) (.own l) ≤ (Tot q + HP q) (.own l))
    (hNE : NoEdgeUnpl Eg c) (hFP : FgnPromClosG Eg c) (hNP : NonPromLbl Eg c) (hBS : TermBoxZ.BoxSto Eg)
    (hMC : MemRtsCG (EgP Eg P N j n) Tot HP2 (promise c j a v w)) :
    PtrRtsGL (EgP Eg P N j n) Tot HP2 (promise c j a v w) :=
  ⟨ptrRtsG_prom hth hPL hplt hG hkey hNE hFP hNP hBS, lblSto_prom hth hPL hG.2.1,
    gateTmin_prom hth hPL hplt hG.2.2.1 hkey hNE, hMC⟩

/-- **CellOwnerLive** (staging; a run lemma to come): a cell's owner is a thread, and an
ownerless cell is shared. -/
def CellOwnerLive (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ l cl, Eg.sto l = some cl → (∀ i, cl.owner = some i → i < c.ths.size) ∧ (cl.owner = none → Eg.Shared l)

/-- `NonPromLbl` from `SysInvN` (`MemOKP` at the cut of a thread holding the cell: the owner's, or any
thread's at a shared cell). -/
theorem nonPromLbl_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (X : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hCO : CellOwnerLive Eg c)
    {j : Nat} {th : TTh} (hth : c.ths[j]? = some th) : NonPromLbl Eg c := by
  intro u m L hmu hE hall
  obtain ⟨⟨ca, hca, -, -⟩, -⟩ := id hE
  obtain ⟨hlive, hsh⟩ := hCO _ ca hca
  cases ho : ca.owner with
  | some i =>
    have hi := hlive i ho
    have hthi : c.ths[i]? = some c.ths[i] := Array.getElem?_eq_getElem hi
    exact plantEdge_lbl_of_thSys (X.thr i _ hthi) (hall i _ hthi) hmu hE
      (fun ca' h => by rw [hca] at h; cases h; exact Or.inl ho)
  | none =>
    exact plantEdge_lbl_of_thSys (X.thr j th hth) (hall j th hth) hmu hE
      (fun _ _ => Or.inr (hsh ho))

end TermPtrStab
#print axioms TermPtrStab.promInCut_init
#print axioms TermPtrStab.promInCut_thread
#print axioms TermPtrStab.promInCut_threadT
#print axioms TermPtrStab.promInCut_prom
