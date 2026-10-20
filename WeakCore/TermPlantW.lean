/-
**The plant wiring** `ThSys_plantW`: the system's thread invariant `ThSysAt`
across the ghost plant `EgP` of a promise step, for events whose every planted label is a
single-word protocol buffer.  Against the green_sw chain.
-/
import WeakCore.TermPlantR
import WeakCore.TermMainDefs
import WeakCore.TermPlantF
import WeakCore.TermOverCr4
namespace TermPlantW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantR
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## (W0) One label's plant in the global environment -/

/-- `Eg` with label `l` planted at frontier `F` and reader-visible count `Np`. -/
def plant1 (Eg : GEnv) (l : AllocLabel) (F : Ts) (Np : Nat) : GEnv :=
  { Eg with pfr := fun l' => if l' = l then some F else Eg.pfr l'
            ini := fun l' => if l' = l then Np else Eg.ini l' }

/-- Planting an own label keeps every cut's store typing of its owner. -/
theorem cutSto_plant1 {Eg : GEnv} {l : AllocLabel} {F : Ts} {Np j : Nat} {c : Cell}
    (hc : Eg.sto l = some c) (ho : c.owner = some j) : cutSto (plant1 Eg l F Np) j = cutSto Eg j := by
  funext l'
  refine cutSto_congr rfl (fun c' hc' hn => ?_)
  by_cases he : l' = l
  · subst he; rw [hc] at hc'; cases hc'; exact absurd ho hn
  · simp [plant1, GEnv.Shared, he]

/-- (W0) **The raised environment is a cut**: raising `l` (own, of thread `j`) in a frame
environment whose code view is `Cut Eg j S` gives the code view `Cut (plant1 Eg l F Np) j S`. -/
theorem CE_withSto_Cut {η : TEnv} {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {l : AllocLabel}
    {F : Ts} {Np : Nat} {c : Cell} (hE : CE η = Cut Eg j S) (hc : Eg.sto l = some c) (ho : c.owner = some j) :
    CE (η.withSto η.sto (fun l' => if l' = l then Np else η.ini l') (fun l' => if l' = l then some F else η.pfr l')
      η.seen) = Cut (plant1 Eg l F Np) j S := by
  have h1 : η.prog = Eg.prog := congrArg TEnv.prog hE
  have h2 : η.sto = cutSto Eg j := congrArg TEnv.sto hE
  have h3 : η.tid = j := congrArg TEnv.tid hE
  have h4 : η.ini = Eg.ini := congrArg TEnv.ini hE
  have h5 : η.rini = Eg.rini := congrArg TEnv.rini hE
  have h6 : η.pfr = Eg.pfr := congrArg TEnv.pfr hE
  have h7 : η.seen = S := congrArg TEnv.seen hE
  have h8 : η.box = Eg.box := congrArg TEnv.box hE
  have h9 : η.fp = Eg.fpOf j := congrArg TEnv.fp hE
  unfold Cut
  rw [cutSto_plant1 hc ho]
  simp only [CE, TEnv.withSto, plant1, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ## (W1) Transport of the plant's pre-state facts across the promise -/

theorem getElem_push_lt {mem : Memory} {x : Msg} {t : Nat} (h : t < mem.size) :
    (mem.push x)[t]? = mem[t]? := by
  simp [Array.getElem?_push, Nat.ne_of_lt h]

theorem getElem_push_ge {mem : Memory} {x : Msg} {t : Nat} {m : Msg} (h : (mem.push x)[t]? = some m)
    (hne : t ≠ mem.size) : mem[t]? = some m := by
  rw [Array.getElem?_push] at h
  split at h
  · next he => exact absurd he hne
  · exact h

/-- (W1) `HoldW` survives the thread's own promise (the new timestamp is above every old one). -/
theorem HoldW_prom {E : TEnv} {s : St} {l : AllocLabel} {f : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hb : ∀ t, t ∈ s.promises → t < s.mem.size) (h : HoldW E s l f) : HoldW E (promSt s a v w) l f := by
  obtain ⟨t, ht, m, hm, hl, hf, hmin, hni⟩ := h
  have htl := hb t ht
  refine ⟨t, List.mem_append_left _ ht, m, by simp only [promSt]; rw [getElem_push_lt htl]; exact hm, hl, hf,
    fun u hu m' hm' hlo => ?_, hni⟩
  rcases List.mem_append.1 hu with hu | hu
  · have hul := hb u hu
    simp only [promSt] at hm'
    rw [getElem_push_lt hul] at hm'
    exact hmin u hu m' hm' hlo
  · rw [List.mem_singleton] at hu; subst hu; exact Nat.le_of_lt htl

/-- (W1) A message of the promised state other than the new one is an old message. -/
theorem prom_old {s : St} {a : Address} {v : WeakMem.Val} {w : Ts} {t : Nat} {m : Msg}
    (hm : (promSt s a v w).mem[t]? = some m) (hne : t ≠ s.mem.size) : s.mem[t]? = some m :=
  getElem_push_ge hm hne

/-- (W1) `PrefixHeld` survives the thread's own promise. -/
theorem PrefixHeld_prom {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {k : Nat} {a : Address}
    {v : WeakMem.Val} {w : Ts} (h : PrefixHeld E s l c k) : PrefixHeld E (promSt s a v w) l c k := by
  intro Na e us hT hu o ho
  rcases h Na e us hT hu o ho with h | ⟨u, hu', m, hm, hlo⟩
  · exact Or.inl h
  · have hul : u < s.mem.size := (Array.getElem?_eq_some_iff.1 hm).1
    exact Or.inr ⟨u, List.mem_append_left _ hu', m, by simp only [promSt]; rw [getElem_push_lt hul]; exact hm, hlo⟩

/-- (W1) The plant's overtaking bound survives the thread's own promise. -/
theorem hhold_prom {s : St} {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel} {F : Nat}
    {Q : Nat → Prop}
    (h : ∀ o, Q o → ∀ (t : Nat) (m : Msg), t ∉ s.promises → s.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ s.mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩) :
    ∀ o, Q o → ∀ (t : Nat) (m : Msg), t ∉ (promSt s a v w).promises → (promSt s a v w).mem[t]? = some m →
      m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ (promSt s a v w).mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩ := by
  intro o hq t m ht hm hlo
  have hne : t ≠ s.mem.size := fun he => ht (by simp [promSt, he])
  have hm0 := prom_old hm hne
  obtain ⟨t', m', h1, h2, h3, h4⟩ := h o hq t m (fun h' => ht (List.mem_append_left _ h')) hm0 hlo
  have htl : t' < s.mem.size := (Array.getElem?_eq_some_iff.1 h3).1
  exact ⟨t', m', h1, h2, by simp only [promSt]; rw [getElem_push_lt htl]; exact h3, h4⟩

/-! ## (W2) Composing the accounting equations -/

theorem Res.add_right_cancel {a b c : Res} (h : a + c = b + c) : a = b := by
  funext k
  have := congrFun h k
  simp only [Res.add_apply] at this
  omega

/-- (W2) Two steps of the `PAcct` shape compose. -/
theorem acct_trans {H0 H1 H2 c0 c1 c2 d0 d1 d2 : Res}
    (h1 : H1 + c1 + d0 = H0 + c0 + d1) (h2 : H2 + c2 + d1 = H1 + c1 + d2) :
    H2 + c2 + d0 = H0 + c0 + d2 := by
  funext k
  have e1 := congrFun h1 k
  have e2 := congrFun h2 k
  simp only [Res.add_apply] at e1 e2 ⊢
  omega

/-! ## (W2) Keyed credits across the plant: `PromCrK` from the `PromCr` machinery -/

/-- An `OldCr` credit exists at every promise (classically). -/
theorem OldCr_ex (E : TEnv) (s : St) (tw : Ts) : ∃ R, ∀ m, s.mem[tw]? = some m → OldCr E s m tw R := by
  cases hm : s.mem[tw]? with
  | none => exact ⟨.zero, fun m h => by cases h⟩
  | some m =>
    suffices h : ∃ R, OldCr E s m tw R by
      obtain ⟨R, hR⟩ := h
      exact ⟨R, fun m' h => by cases h; exact hR⟩
    by_cases hp : ∃ w, PredAt s.mem m.loc tw w
    · obtain ⟨w, hw⟩ := hp
      by_cases hv : Vis E m.loc.label ∧ IniW E m.loc
      · by_cases hW : ∃ n P, WordAt E m.loc n P ∧ WordHolds P [w.val]
        · obtain ⟨n, P, h1, h2⟩ := hW
          exact ⟨_, Or.inl ⟨w, hw, Or.inl ⟨hv.1, hv.2, Or.inl ⟨n, P, h1, h2, rfl⟩⟩⟩⟩
        · exact ⟨_, Or.inl ⟨w, hw, Or.inl ⟨hv.1, hv.2, Or.inr ⟨fun n P h1 h2 => hW ⟨n, P, h1, h2⟩, rfl⟩⟩⟩⟩
      · exact ⟨_, Or.inl ⟨w, hw, Or.inr ⟨hv, rfl⟩⟩⟩
    · exact ⟨_, Or.inr ⟨fun w h => hp ⟨w, h⟩, rfl⟩⟩

/-! ### (dedup) `KeepNW` and the credit-lift master -/

/-- Old promises `P` at units that are not word units of `E` keep their credit `cr`. -/
def KeepNW (E : TEnv) (mem : Memory) (P : List Ts) (cr cr' : Ts → Res) : Prop :=
  ∀ tw m, tw ∈ P → mem[tw]? = some m → ¬ WordUnit E m.loc → cr' tw = cr tw

theorem KeepNW_refl {E : TEnv} {mem : Memory} {P : List Ts} {cr : Ts → Res} : KeepNW E mem P cr cr :=
  fun _ _ _ _ _ => rfl

theorem KeepNW_trans {E : TEnv} {mem : Memory} {P : List Ts} {cr cr1 cr2 : Ts → Res}
    (h1 : KeepNW E mem P cr cr1) (h2 : KeepNW E mem P cr1 cr2) : KeepNW E mem P cr cr2 :=
  fun tw m ht hm hw => (h2 tw m ht hm hw).trans (h1 tw m ht hm hw)

theorem KeepNW_of_sto {E E' : TEnv} {mem : Memory} {P : List Ts} {cr cr' : Ts → Res}
    (h : KeepNW E mem P cr cr') (hs : E.sto = E'.sto) : KeepNW E' mem P cr cr' :=
  fun tw m ht hm hw => h tw m ht hm fun hu => hw ((WordUnit_congr (by rw [hs])).1 hu)

/-- Re-key the `KeepNW` conjunct of a plant step to an environment with the same store typing. -/
theorem exK_sto {E E' : TEnv} {mem : Memory} {L : List Ts} {cr : Ts → Res}
    {P Q : Res → Res → (Ts → Res) → (Ts → Res) → Prop} (hs : E.sto = E'.sto)
    (h : ∃ a b c d, P a b c d ∧ Q a b c d ∧ KeepNW E mem L cr c) :
    ∃ a b c d, P a b c d ∧ Q a b c d ∧ KeepNW E' mem L cr c := by
  obtain ⟨a, b, c, d, h1, h2, h3⟩ := h
  exact ⟨a, b, c, d, h1, h2, KeepNW_of_sto h3 hs⟩

/-- (dedup) **The credit lift**, master of `PromCrK_lift`/`PromCrK_liftQ` (and their `K` forms):
the old promises off `Ql` keep their credit at non-word units once the store typing agrees. -/
theorem PromCrK_liftG {E E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {Ql : AllocLabel → Prop}
    (hC : TermPlant.PromCrK E s cr db)
    (hPl : ∀ tw m R, s.mem[tw]? = some m → PlantCr E s m tw R → ¬ Ql m.loc.label)
    (hPT : ∀ tw m R, s.mem[tw]? = some m → ¬ Ql m.loc.label → PlantCr E s m tw R → PlantCr E2 s m tw R)
    (hstep : ∀ cr0 : Ts → Res, PromCr E s cr0 db → ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → ¬ Ql m.loc.label → cr2 tw = cr0 tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr0 + pSum s db2) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ TermPlant.PromCrK E2 s cr2 db2 ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 ∧
      ((∀ l, E2.sto l = E.sto l) → KeepNW E s.mem s.promises cr cr2) := by
  classical
  let Q : Ts → Bool := fun tw => decide (∃ m, s.mem[tw]? = some m ∧ ¬ OldCr E s m tw (cr tw))
  let cr0 : Ts → Res := fun tw => if Q tw then Classical.choose (OldCr_ex E s tw) else cr tw
  have hC0 : PromCr E s cr0 db := by
    intro tw htw
    obtain ⟨m, hm, hd, -⟩ := hC tw htw
    refine ⟨m, hm, hd, ?_⟩
    show OldCr E s m tw (cr0 tw)
    by_cases hq : Q tw = true
    · simp only [cr0, hq, ite_true]; exact Classical.choose_spec (OldCr_ex E s tw) m hm
    · have hq' : Q tw = false := by simpa using hq
      simp only [cr0, hq', Bool.false_eq_true, ite_false]
      simp only [Q, decide_eq_false_iff_not, not_exists, not_and, Classical.not_not] at hq'
      exact hq' m hm
  obtain ⟨H2, cr2', db2, hH2, hC2, hk, heq⟩ := hstep cr0 hC0
  let cr2 : Ts → Res := fun tw => if Q tw then cr tw else cr2' tw
  -- the swapped promises are plant credits, off `l`
  have hQ : ∀ tw, tw ∈ s.promises → Q tw = true → ∃ m, s.mem[tw]? = some m ∧ ¬ Ql m.loc.label ∧
      PlantCr E s m tw (cr tw) ∧ TermPlant.CrKeys (cr tw) := by
    intro tw htw hq
    simp only [Q, decide_eq_true_eq] at hq
    obtain ⟨m, hm, hno⟩ := hq
    obtain ⟨m', hm', -, hor⟩ := hC tw htw
    rw [hm] at hm'; cases hm'
    rcases hor with h | h
    · exact absurd h hno
    · exact ⟨m, hm, hPl tw m _ hm h.1, h.1, h.2⟩
  refine ⟨H2, cr2, db2, hH2, fun tw htw => ?_, ?_, ?_⟩
  · obtain ⟨m, hm, hd, hor⟩ := hC2 tw htw
    refine ⟨m, hm, hd, ?_⟩
    by_cases hq : Q tw = true
    · obtain ⟨m', hm', hla, hp, hkey⟩ := hQ tw htw hq
      rw [hm] at hm'; cases hm'
      simp only [cr2, hq, ite_true]
      exact Or.inr ⟨hPT tw m _ hm hla hp, hkey⟩
    · have hq' : Q tw = false := by simpa using hq
      simp only [cr2, hq', Bool.false_eq_true, ite_false]
      exact Or.inl hor
  · have hk' : ∀ tw, tw ∈ s.promises → Q tw = true → cr2' tw = cr0 tw := fun tw htw hq => by
      obtain ⟨m, hm, hla, -⟩ := hQ tw htw hq
      exact (hk tw m htw hm hla).1
    unfold pSum at heq ⊢
    rw [Res.sum_filter_split cr2 Q, Res.sum_filter_split cr Q] 
    rw [Res.sum_filter_split cr2' Q, Res.sum_filter_split cr0 Q] at heq
    have a1 : Res.sum ((s.promises.filter Q).map cr2') = Res.sum ((s.promises.filter Q).map cr0) :=
      Res.sum_map_congr fun t ht => by rw [List.mem_filter] at ht; exact hk' t ht.1 ht.2
    have a2 : Res.sum ((s.promises.filter Q).map cr2) = Res.sum ((s.promises.filter Q).map cr) :=
      Res.sum_map_congr fun t ht => by rw [List.mem_filter] at ht; simp only [cr2, ht.2, ite_true]
    have a3 : Res.sum ((s.promises.filter (fun t => !Q t)).map cr2) =
        Res.sum ((s.promises.filter (fun t => !Q t)).map cr2') :=
      Res.sum_map_congr fun t ht => by
        rw [List.mem_filter, Bool.not_eq_true'] at ht; simp only [cr2, ht.2, Bool.false_eq_true, ite_false]
    have a4 : Res.sum ((s.promises.filter (fun t => !Q t)).map cr0) =
        Res.sum ((s.promises.filter (fun t => !Q t)).map cr) :=
      Res.sum_map_congr fun t ht => by
        rw [List.mem_filter, Bool.not_eq_true'] at ht; simp only [cr0, ht.2, Bool.false_eq_true, ite_false]
    rw [a1, a4] at heq
    rw [a2, a3]
    funext k
    have e := congrFun heq k
    simp only [Res.add_apply] at e ⊢
    omega
  · intro hsto tw m htw hm hnw
    by_cases hq : Q tw = true
    · simp only [cr2, hq, ite_true]
    · have hq' : Q tw = false := by simpa using hq
      simp only [cr2, hq', Bool.false_eq_true, ite_false]
      obtain ⟨m2, hm2, -, hor⟩ := hC2 tw htw
      rw [hm] at hm2; cases hm2
      have z1 : cr2' tw = .zero :=
        TermOverCr4.oldCr_nword_zero (E := E2) (s := s) (fun h => hnw ((WordUnit_congr (hsto _)).1 h)) hor
      simp only [Q, decide_eq_false_iff_not, not_exists, not_and, Classical.not_not] at hq'
      have z2 : cr tw = .zero := TermOverCr4.oldCr_nword_zero hnw (hq' m hm)
      rw [z1, z2]

theorem PromCrK_liftQK {E E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {Ql : AllocLabel → Prop}
    (hC : TermPlant.PromCrK E s cr db)
    (hPl : ∀ tw m R, s.mem[tw]? = some m → PlantCr E s m tw R → ¬ Ql m.loc.label)
    (hPT : ∀ tw m R, s.mem[tw]? = some m → ¬ Ql m.loc.label → PlantCr E s m tw R → PlantCr E2 s m tw R)
    (hstep : ∀ cr0 : Ts → Res, PromCr E s cr0 db → ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → ¬ Ql m.loc.label → cr2 tw = cr0 tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr0 + pSum s db2)
    (hsto : ∀ l, E2.sto l = E.sto l) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ TermPlant.PromCrK E2 s cr2 db2 ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 ∧ KeepNW E s.mem s.promises cr cr2 :=
  let ⟨H2, cr2, db2, h1, h2, h3, h4⟩ := PromCrK_liftG hC hPl hPT hstep
  ⟨H2, cr2, db2, h1, h2, h3, h4 hsto⟩

theorem PromCrK_liftK {E E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {l : AllocLabel}
    (hC : TermPlant.PromCrK E s cr db)
    (hPl : ∀ tw m R, s.mem[tw]? = some m → PlantCr E s m tw R → m.loc.label ≠ l)
    (hPT : ∀ tw m R, s.mem[tw]? = some m → m.loc.label ≠ l → PlantCr E s m tw R → PlantCr E2 s m tw R)
    (hstep : ∀ cr0 : Ts → Res, PromCr E s cr0 db → ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → m.loc.label ≠ l → cr2 tw = cr0 tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr0 + pSum s db2)
    (hsto : ∀ l, E2.sto l = E.sto l) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ TermPlant.PromCrK E2 s cr2 db2 ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 ∧ KeepNW E s.mem s.promises cr cr2 :=
  PromCrK_liftQK (Ql := (· = l)) hC hPl hPT hstep hsto

/-- (W2) **`PromCrK_lift`**: a memory/credit step proved for `PromCr` (keeping credits off `l`)
carries `PromCrK`, provided plant credits sit off `l` and survive the step.  The plant credits
are swapped for `OldCr` ones before the step and back after it. -/
theorem PromCrK_lift {E E2 : TEnv} {s : St} {H : Res} {cr db : Ts → Res} {l : AllocLabel}
    (hC : TermPlant.PromCrK E s cr db)
    (hPl : ∀ tw m R, s.mem[tw]? = some m → PlantCr E s m tw R → m.loc.label ≠ l)
    (hPT : ∀ tw m R, s.mem[tw]? = some m → m.loc.label ≠ l → PlantCr E s m tw R → PlantCr E2 s m tw R)
    (hstep : ∀ cr0 : Ts → Res, PromCr E s cr0 db → ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ PromCr E2 s cr2 db2 ∧
      (∀ tw m, tw ∈ s.promises → s.mem[tw]? = some m → m.loc.label ≠ l → cr2 tw = cr0 tw ∧ db2 tw = db tw) ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr0 + pSum s db2) :
    ∃ H2 cr2 db2, MemHeld E2 s H2 ∧ TermPlant.PromCrK E2 s cr2 db2 ∧
      H2 + pSum s cr2 + pSum s db = H + pSum s cr + pSum s db2 := by
    obtain ⟨x0, x1, x2, h0, h1, h2, -⟩ := PromCrK_liftG (Ql := (· = l)) hC hPl hPT hstep
    exact ⟨x0, x1, x2, h0, h1, h2⟩

/-! ## (W3) One label's plant at the thread's system invariant -/

/-- (dedup) master of `ThSysAt_plant1`: also exports `KeepNW` (old non-word credits kept). -/
theorem ThSysAt_plant1K {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell} {N n : Nat}
    {P : Proto} {F Np : Ts}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg.pfr l = none)
    (hTc : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hrl : Eg.rini l ≤ Eg.ini l) (hNp : Eg.ini l ≤ Np) (hNN : Np ≤ N)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg g.i S) (stOf mem pairs th) l F)
    (hFw : Eg.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F)
    (hhold : ∀ o, InitR (Cut (plant1 Eg l F Np) g.i S) c l o → ¬ InitR (Cut Eg g.i S) c l o →
      ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩)
    (hinh : ∀ b S' us, SegOf c.ty b S' → accs S' = some us →
      IniSeg (Cut (plant1 Eg l F Np) g.i S) c l b → ¬ IniSeg (Cut Eg g.i S) c l b →
      ∃ ws, ValOf (Cut (plant1 Eg l F Np) g.i S) S' ws ∧ ws.length = nWords us)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th))
    (hR1w : ∀ j, Eg.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises)
    (hval : ∀ j, Eg.ini l ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w →
      ∃ R, ValOfR (Cut (plant1 Eg l F Np) g.i S) (.word (.lit n) P) [w] R) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' ∧
      KeepNW (Cut Eg g.i S) mem th.promises cr cr' := by
  obtain ⟨hRE, hTE, hm, hHP, hHS, hC⟩ := h
  have hH : MemHeld (Cut Eg g.i S) (stOf mem pairs th) (HP + HS) :=
    MemHeld_join (fun _ _ h1 h2 => Cut_cov h1 h2) hHP hHS
  obtain ⟨ρ, η, cx, Rf, Rs, hE0, hE, hTy, htv, hFI, hsum⟩ := hRE
  have e2 := CE_withSto_Cut (F := F) (Np := Np) hE0 hc ho
  rw [← e2] at hhold hinh hval
  rw [← hE0] at hm hH hC hF hf hfo hhold hinh
  have hsto : η.sto l = some c := by
    show (CE η).sto l = some c
    rw [hE0]; exact cutSto_own hc ho
  have htid : η.tid = g.i := congrArg TEnv.tid hE0
  have hown : c.owner = some η.tid := by rw [htid]; exact ho
  have hnone' : η.pfr l = none := by
    show (CE η).pfr l = none
    rw [hE0]; exact hnone
  have hini : η.ini = Eg.ini := congrArg TEnv.ini hE0
  have hrini : η.rini = Eg.rini := congrArg TEnv.rini hE0
  rw [← hini] at hNp hFw hR1w hval
  rw [← hrini, ← hini] at hrl
  let P1 : AllocLabel → Option Ts := fun l' => if l' = l then some F else η.pfr l'
  let I2 : AllocLabel → Nat := fun l' => if l' = l then Np else η.ini l'
  have hP1 : ∀ l' f, η.pfr l' = some f → P1 l' = some f := fun l' f h => by
    by_cases he : l' = l
    · subst he; rw [hnone'] at h; cases h
    · simp [P1, he, h]
  have hI2 : ∀ l', η.ini l' ≤ I2 l' := fun l' => by
    by_cases he : l' = l
    · subst he; simp [I2, hNp]
    · simp [I2, he]
  have hx : Ext η (η.withSto η.sto I2 P1 η.seen) :=
    Ext_withSto hE.2.1 (fun _ _ h => h) hI2 hP1
  have hE' : EnvOK p (η.withSto η.sto I2 P1 η.seen) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hMI := MemInv_plantFN (E' := CE (η.withSto η.sto I2 P1 η.seen)) (N := Np) hm hsto hown hnone'
    rfl rfl rfl rfl hNp hrl rfl rfl rfl hF hFw hhold hinh hcpl hcT hnT hrT
  have hnd : th.promises.Nodup := MemInv_nodup hm
  -- the memory and credit step, keyed
  have hV2 : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfR (CE η) T vs R →
      ValOfR (CE (η.withSto η.sto I2 P1 η.seen)) T vs R := fun h =>
    ValOfR_mono (η₁ := CE η) (η₂ := CE (η.withSto η.sto I2 P1 η.seen)) rfl rfl
      (fun _ _ h => h) hI2 h hP1 (fun _ _ h => h) (fun _ => Nat.le_refl _)
  obtain ⟨H', cr', db', hH', hC', heq, hKN⟩ := PromCrK_liftK (hsto := fun _ => rfl) (E2 := CE (η.withSto η.sto I2 P1 η.seen)) (l := l) hC
    (fun tw m R hm' hp hla => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hpf, -⟩ := hp
      exact hpf (by rw [hla]; exact hnone'))
    (fun tw m R hm' hla hp => TermPlant.PlantCr_mono (E := CE η) (E' := CE (η.withSto η.sto I2 P1 η.seen)) (s := stOf mem pairs th) (s' := stOf mem pairs th)
      (fun _ _ => rfl) (Nat.le_refl _) rfl (MemInv_promLt hm) rfl rfl
      (fun h => by
        show P1 m.loc.label ≠ none
        simp only [P1, hla, ite_false]; exact h)
      (fun h => (WordUnit_congr rfl).1 h)
      (fun _ _ h => by
        have hvq : Vis (CE (η.withSto η.sto I2 P1 η.seen)) m.loc.label ↔ Vis (CE η) m.loc.label :=
          Vis_congr rfl rfl (by show P1 m.loc.label = η.pfr m.loc.label; simp [P1, hla])
        unfold FpAt at h ⊢; rw [hvq] at h; exact h)
      (fun S ws R0 h => hV2 h) hp)
    (fun cr0 hC0 => MemHeld_plantW (E := CE η)
      (E1 := CE (η.withSto η.sto η.ini P1 η.seen)) (E2 := CE (η.withSto η.sto I2 P1 η.seen))
      (c := c) (N := N) (n := n) (P := P)
      hm hH hC0 hpa (fun _ => rfl) (fun _ => rfl)
      (fun l' hv hpr => hv ⟨hpr.1, by
        by_cases he : l' = l
        · subst he; have := hpr.2; simp [CE, TEnv.withSto, P1] at this
        · have := hpr.2; simpa [CE, TEnv.withSto, P1, he] using this⟩)
      (fun l' hne hv hpr => hv ⟨hpr.1, by simpa [CE, TEnv.withSto, P1, hne] using hpr.2⟩)
      (fun h => ValOfR_mono (η₁ := CE η) (η₂ := CE (η.withSto η.sto η.ini P1 η.seen)) rfl rfl
        (fun _ _ h => h) (fun _ => Nat.le_refl _) h hP1 (fun _ _ h => h) (fun _ => Nat.le_refl _))
      hf hfo ⟨c, hsto, hown⟩
      (fun l' hne => by
        by_cases he : l' = l
        · subst he; simp [CE, TEnv.withSto, P1]
        · simpa [CE, TEnv.withSto, P1, he] using hne)
      (fun l' hne h1 => by simpa [CE, TEnv.withSto, P1, hne] using h1)
      rfl (fun _ => rfl) rfl (fun _ _ h => h) (fun _ => rfl)
      (fun l' hne => by simp [CE, TEnv.withSto, I2, hne]) rfl (fun _ => rfl) rfl (fun _ => rfl)
      hsto hTc hP
      (fun h => ValOfR_mono (η₁ := CE (η.withSto η.sto η.ini P1 η.seen))
        (η₂ := CE (η.withSto η.sto I2 P1 η.seen)) rfl rfl (fun _ _ h => h) hI2 h (fun _ _ h => h)
        (fun _ _ h => h) (fun _ => Nat.le_refl _))
      (by simp [CE, TEnv.withSto, I2, hNp]) (by simp [CE, TEnv.withSto, I2, hNN]) hrl
      (by simp [CE, TEnv.withSto, P1]) (fun _ _ h => h) hnd
      (fun j h1 h2 => hR1w j h1 (by simpa [CE, TEnv.withSto, I2] using h2))
      (fun j h1 h2 => hval j h1 (by simpa [CE, TEnv.withSto, I2] using h2)))
  -- the plain invariant at the raised environment
  have hTE' : ThInvE p (CE (η.withSto η.sto I2 P1 η.seen)) th := by
    obtain ⟨ρe, ηe, cxe, hEe0, hEe, hTye, htve, hFIe⟩ := hTE
    have hce : CE ηe = CE η := hEe0.trans hE0.symm
    have q1 : ηe.sto = η.sto := (congrArg TEnv.sto hce : (CE ηe).sto = (CE η).sto)
    have q2 : ηe.ini = η.ini := (congrArg TEnv.ini hce : (CE ηe).ini = (CE η).ini)
    have q3 : ηe.pfr = η.pfr := (congrArg TEnv.pfr hce : (CE ηe).pfr = (CE η).pfr)
    have q4 : ηe.seen = η.seen := (congrArg TEnv.seen hce : (CE ηe).seen = (CE η).seen)
    have hxe : Ext ηe (ηe.withSto ηe.sto I2 P1 ηe.seen) :=
      Ext_withSto hEe.2.1 (fun _ _ h => h) (fun l' => by rw [q2]; exact hI2 l')
        (fun l' f h => hP1 l' f (by rw [← q3]; exact h))
    refine ⟨ρe, ηe.withSto ηe.sto I2 P1 ηe.seen, cxe, ?_, ⟨hEe.1, hxe.1, hxe.2.2.2.2.2.2.2.2.2.2.1⟩, hTye, htve, FInv_ext hEe.2.1 hxe hFIe.1, hFIe.2⟩
    have q5 : ηe.prog = η.prog := (congrArg TEnv.prog hce : (CE ηe).prog = (CE η).prog)
    have q6 : ηe.tid = η.tid := (congrArg TEnv.tid hce : (CE ηe).tid = (CE η).tid)
    have q7 : ηe.rini = η.rini := (congrArg TEnv.rini hce : (CE ηe).rini = (CE η).rini)
    have q8 : ηe.box = η.box := (congrArg TEnv.box hce : (CE ηe).box = (CE η).box)
    have q9 : ηe.fp = η.fp := (congrArg TEnv.fp hce : (CE ηe).fp = (CE η).fp)
    simp only [CE, TEnv.withSto, q1, q4, q5, q6, q7, q8, q9]
  have hRE' : ThInvRE p (CE (η.withSto η.sto I2 P1 η.seen)) th Tot :=
    ⟨ρ, _, cx, Rf, Rs, rfl, hE', hTy, htv, FInvR_ext hE.2.1 hE.2.2 hx hFI, hsum⟩
  -- back to the cut, and split the holding
  have e2' : CE (η.withSto η.sto I2 P1 η.seen) = Cut (plant1 Eg l F Np) g.i S := e2
  rw [e2'] at hRE' hTE' hMI hH' hC'
  obtain ⟨HP', HS', rfl, hP', hS'⟩ := MemHeld_split (fun _ _ h1 h2 => Cut_cov h1 h2) hH'
  exact ⟨HP', HS', cr', db', ⟨hRE', hTE', hMI, hP', hS', hC'⟩, heq, by rw [hE0] at hKN; exact hKN⟩

/-- (W3) **`ThSysAt_plant1`**: planting one single-word protocol buffer `l` of thread `g.i`
(frontier `F`, reader-visible count `Np`) keeps the thread's system invariant at the same `seen`
set, memory's holding and the keyed credits moving by an equality of totals.  The side conditions
are the plant's (`MemInv_plantFN`, `FlipOK`, `FpOK`) and, at each newly counted unit, the
placeholder-then-own-promises shape (`R1w`) and a value reading (`R3`), stated at the cut before
(`Cut Eg g.i S`) and after (`Cut (plant1 Eg l F Np) g.i S`). -/
theorem ThSysAt_plant1 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell} {N n : Nat}
    {P : Proto} {F Np : Ts}
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hpa : PromAbove (stOf mem pairs th))
    (hc : Eg.sto l = some c) (ho : c.owner = some g.i) (hnone : Eg.pfr l = none)
    (hTc : c.ty = .array (.lit N) (.word (.lit n) P)) (hP : P.ghost = false)
    (hrl : Eg.rini l ≤ Eg.ini l) (hNp : Eg.ini l ≤ Np) (hNN : Np ≤ N)
    (hF : F ≤ (stOf mem pairs th).vs.vWr ∨ HoldW (Cut Eg g.i S) (stOf mem pairs th) l F)
    (hFw : Eg.ini l < Np → (stOf mem pairs th).vs.vWr ≤ F)
    (hhold : ∀ o, InitR (Cut (plant1 Eg l F Np) g.i S) c l o → ¬ InitR (Cut Eg g.i S) c l o →
      ∀ (t : Nat) (m : Msg), t ∉ th.promises → mem[t]? = some m → m.loc = ⟨l, o⟩ →
      ∃ (t' : Nat) (m' : Msg), t < t' ∧ t' ≤ F ∧ mem[t']? = some m' ∧ m'.loc = ⟨l, o⟩)
    (hinh : ∀ b S' us, SegOf c.ty b S' → accs S' = some us →
      IniSeg (Cut (plant1 Eg l F Np) g.i S) c l b → ¬ IniSeg (Cut Eg g.i S) c l b →
      ∃ ws, ValOf (Cut (plant1 Eg l F Np) g.i S) S' ws ∧ ws.length = nWords us)
    (hcpl : ∀ b S', SegOf c.ty b S' → accs S' ≠ none → TearOK S') (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hf : FlipOK (Cut Eg g.i S) (stOf mem pairs th) l) (hfo : FpOK (Cut Eg g.i S) (stOf mem pairs th))
    (hR1w : ∀ j, Eg.ini l ≤ j → j < Np → ∃ t0 m0, mem[t0]? = some m0 ∧ m0.loc = ⟨l, j⟩ ∧
      m0.val = .undef ∧ t0 ∉ th.promises ∧ (∃ t, AtA mem ⟨l, j⟩ t0 t = true) ∧
      ∀ t m, mem[t]? = some m → m.loc = ⟨l, j⟩ → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ th.promises)
    (hval : ∀ j, Eg.ini l ≤ j → j < Np → ∀ w, LatestNP mem [] ⟨l, j⟩ w →
      ∃ R, ValOfR (Cut (plant1 Eg l F Np) g.i S) (.word (.lit n) P) [w] R) :
    ∃ HP' HS' cr' db', ThSysAt p g mem pairs th (plant1 Eg l F Np) Tot HP' HS' cr' db' S ∧
      (HP' + HS') + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db =
        (HP + HS) + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' := by
    obtain ⟨x0, x1, x2, x3, h0, h1, -⟩ := ThSysAt_plant1K h hpa hc ho hnone hTc hP hrl hNp hNN hF hFw hhold hinh hcpl hcT hnT hrT hf hfo hR1w hval
    exact ⟨x0, x1, x2, x3, h0, h1⟩

#print axioms CE_withSto_Cut
#print axioms HoldW_prom
#print axioms PrefixHeld_prom
#print axioms hhold_prom
#print axioms acct_trans
#print axioms PromCrK_lift
#print axioms ThSysAt_plant1

#print axioms KeepNW_refl
#print axioms KeepNW_trans
#print axioms KeepNW_of_sto
#print axioms exK_sto
#print axioms PromCrK_liftG
#print axioms PromCrK_liftQK
#print axioms PromCrK_liftK
#print axioms ThSysAt_plant1K

end TermPlantW
