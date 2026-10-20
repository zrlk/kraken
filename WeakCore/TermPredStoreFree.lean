import WeakCore.TermPredHoldP
import WeakCore.TermStoreNI
import WeakCore.TermSeenHid
import WeakCore.TermViewInvH
import WeakCore.TermLocal
import WeakCore.TermB5
import WeakCore.TermPlant
namespace TermPredStoreFree
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## COPIED LEMMAS (verbatim copies of TermPlantViewM: not_seen_of_rc, dep_of_modeOK, pv_leaf; and of
TermPlantViewC: dep_le_storeOb, storeUnits_keepLow, mth', dep_le_dTs, stepRmw_keepLow).  Those modules
are not in W; drop this block and use the originals if they land. -/

namespace PVc
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermCut TermSys TermMain TermCert TermFul TermLiveProps
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (r1) **A label below its visible count is unseen**, at any thread environment satisfying `MemInv`. -/
theorem not_seen_of_rc {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) {x : AllocLabel} {c : Cell}
    (hsto : E.sto x = some c) (hlt : E.rc x < E.ini x) (hz : ¬ ZW E x) : ¬ E.seen x := by
  intro hs
  have hown := hm.2.2.2.2.2.1.2
  have hso := hm.2.2.2.2.2.2.2.2.1.1
  by_cases ho : c.owner = some E.tid
  · obtain ⟨f, -, hns, -⟩ := hown x c hsto ho hlt
    exact hns hz hs
  · rcases hso x hs with ⟨c', hc', ho'⟩ | ⟨hn, -⟩
    · rw [hsto] at hc'; cases hc'; exact ho ho'
    · rw [hsto] at hn; cases hn

/-- **The bound from `ModeOK .pub`**: a pub handle word to an unseen label with frontier `F`
has `F ≤ dep k w`, given `view ≤ rts`. -/
theorem dep_of_modeOK {k : Promises.Knobs} {i : Nat} {P : AllocLabel → Option Ts} {S : AllocLabel → Prop}
    {x : AllocLabel} {c : Cell} {w : Word} {F : Ts}
    (hmo : ModeOK i P S .pub x c [w]) (hP : P x = some F) (hS : ¬ S x) (hvr : w.view ≤ w.rts) :
    F ≤ TermStoreNI.dep k w := by
  obtain ⟨f, hf, h⟩ := hmo
  rw [hP] at hf; cases hf
  have hv : F ≤ w.view := h.resolve_left hS w (List.mem_singleton_self _)
  unfold TermStoreNI.dep
  split
  · exact Nat.le_trans hv hvr
  · exact hv

/-- **PlantView's leaf, discharged**: at a thread environment `E` with `MemInv`, a pub handle word
`w` (`ModeOK` at `E`) into a planted-unseen-predicted `x` (`pfr x = F`, `rc x < ini x`) has
`F ≤ dep k w`. -/
theorem pv_leaf {k : Promises.Knobs} {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) {x : AllocLabel}
    {c : Cell} {w : Word} {F : Ts} (hsto : E.sto x = some c) (hmo : ModeOK E.tid E.pfr E.seen .pub x c [w])
    (hP : E.pfr x = some F) (hlt : E.rc x < E.ini x) (hz : ¬ ZW E x) (hvr : w.view ≤ w.rts) :
    F ≤ TermStoreNI.dep k w :=
  dep_of_modeOK hmo hP (not_seen_of_rc hm hsto hlt hz) hvr


theorem dep_le_storeOb (k : Promises.Knobs) (arch : Arch) (s : St) (pw w : Word) (b : Address) :
    TermStoreNI.dep k pw ≤ Promises.storeOb k arch (mth s pw w w) b (dataE 1 w) [0] :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (TermStoreNI.Bnd_le_storeOb k arch s pw w b)

/-- **Consumer (store).** A promise at or below `F ≤ dep k pw` survives a store through `pw`. -/
theorem storeUnits_keepLow {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} (hs : s' ∈ storeUnits k arch pw a rel us ws i s)
    {u F : Ts} (hu : u ∈ s.promises) (huF : u ≤ F) (hF : F ≤ TermStoreNI.dep k pw) :
    u ∈ s'.promises := by
  refine Classical.byContradiction fun hx => ?_
  obtain ⟨-, -, rem⟩ := storeUnits_ful us ws i s s' hs
  obtain ⟨j, w, s0, m, -, -, -, -, -, -, -, -, hob⟩ := rem u hu hx
  exact Nat.lt_irrefl u (Nat.lt_of_le_of_lt (Nat.le_trans huF (Nat.le_trans hF
    (dep_le_storeOb k arch s0 pw w (offs a (i + j))))) hob)


abbrev mth' (pw nw : Word) := regsOf pw nw nw

theorem dep_le_dTs (k : Promises.Knobs) (pw nw : Word) :
    TermStoreNI.dep k pw ≤ (if k.storeDepRts then
        Promises.depRts (mth' pw nw) ((dataE 1 nw).writeDeps [0])
      else Promises.depView (mth' pw nw) ((dataE 1 nw).writeDeps [0])) := by
  generalize dataE 1 nw = e
  cases e <;>
  · unfold TermStoreNI.dep Promises.depRts Promises.depView
    simp only [WeakMem.Expr.writeDeps, List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    cases k.storeDepRts <;> simp only [mth', regsOf, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact Nat.le_max_right _ _ | exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

/-- **Consumer (rmw).** A promise at or below `F ≤ dep k pw` survives an RMW through `pw`. -/
theorem stepRmw_keepLow_at {k : Promises.Knobs} {arch : Arch} {s : St} {pw nw : Word} {mem' : Memory}
    {th' : Promises.Thread} {b : Address} {kind : WeakMem.RmwKind} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch s.mem s.pairs (mth s pw nw nw) 1 b kind (dataE 1 nw) [0] acq rel)
    {u F : Ts} (hu : u ∈ s.promises) (huF : u ≤ F) (hF : F ≤ TermStoreNI.dep k pw) :
    u ∈ th'.promises := by
  have hd := dep_le_dTs k pw nw
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [lockFence_prom]; exact hu
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rw [lockFence_prom]; exact hu
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : s.mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, -, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨⟨⟨-, -⟩, -⟩, hlt⟩, -⟩ := hcond
          rw [lockFence_prom]
          show u ∈ s.promises.erase tw
          have hne : u ≠ tw := by
            intro e; subst e
            have : TermStoreNI.dep k pw < u := Nat.lt_of_le_of_lt (Nat.le_trans hd (by
              simp only [mth] at hlt ⊢; split <;> maxle)) hlt
            exact Nat.lt_irrefl u (Nat.lt_of_le_of_lt (Nat.le_trans huF hF) this)
          exact (List.mem_erase_of_ne hne).2 hu

theorem stepRmw_keepLow {k : Promises.Knobs} {arch : Arch} {s : St} {pw nw : Word} {mem' : Memory}
    {th' : Promises.Thread} {b : Address} {kind : WeakMem.RmwKind} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch s.mem s.pairs (mth s pw nw nw) 1 b kind (dataE 1 nw) [0] acq rel)
    {u F : Ts} (hu : u ∈ s.promises) (huF : u ≤ F) (hF : F ≤ TermStoreNI.dep k pw) :
    u ∈ th'.promises := by
  have h' : (mem', th') ∈ Promises.stepRmwAt k arch (lockS arch s).mem (lockS arch s).pairs
      (mth (lockS arch s) pw nw nw) 1 b kind (dataE 1 nw) [0] acq rel := by
    rw [lockS_mem, lockS_pairs, ← lock_mth]; exact h
  exact stepRmw_keepLow_at h' (by rw [lockS_prom]; exact hu) huF hF

end PVc

def UnitsAtRc (η : TEnv) (b : Address) (us : List Acc) : Prop :=
  ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧ IniAt (modeIni .own η.ini η.rini) c b U

theorem ptr_targetM {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧
      ModeOK η.tid η.pfr η.seen μ b.label c [pw] ∧ IniAt (modeIni μ η.ini η.rini) c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VR] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, hmo, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, hmo, fun N e hc => ?_⟩
    · rw [hoff]; exact Fd_AtOff Fd.refl hacc
    · rw [hc] at hacc; simp [accs] at hacc
  · simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, hmo, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, hmo, hini⟩

theorem xchgAt_uaR {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, hini, -, -,
        htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus,
        hini⟩

theorem xchgAtF_uaR {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
        hsku, hsig, htbu, hiniV⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), ?_⟩
      · simpa [offs, Nat.add_assoc] using AtOff_trans hat hato
      · have h := hiniV _ _ hato
        simpa [offs, Nat.add_assoc] using h

theorem stl_uaR {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, -, hini, hsku, -⟩ :=
        slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], hini⟩

theorem stlw_uaR {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, -, hini,
        hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], hini⟩
/-! ## Targets with the reference's mode -/

def TI (η : TEnv) (b : Address) (us : List Acc) (pw : Word) : Prop :=
  ∃ c U μ, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
    ModeOK η.tid η.pfr η.seen μ b.label c [pw] ∧ IniAt (modeIni μ η.ini η.rini) c b U ∧ (μ = .own ∨ μ = .pub)

theorem mode_eq {t u u' : Ty} {μ μ' : Mode} (ht : t = .ptr μ u ∨ t = .loc μ u)
    (ht' : t = .ptr μ' u' ∨ t = .loc μ' u') : μ = μ' := by
  rcases ht with rfl | rfl <;> rcases ht' with h | h <;> cases h <;> rfl

theorem mode_ok {t u u' : Ty} {μ μ' : Mode} (ht : t = .ptr μ u ∨ t = .loc μ u)
    (ht' : t = .ptr μ' u' ∨ t = .loc μ' u') (hμ' : μ' = .own ∨ μ' = .pub) : μ = .own ∨ μ = .pub := by
  rw [mode_eq ht ht']; exact hμ'

theorem mode_of_cell {t u : Ty} {μ : Mode} (hc : cellOf t = some (μ, u))
    (hns : ∀ r u, cellOf t ≠ some (.rgn r, u)) : μ = .own ∨ μ = .pub := by
  cases μ with
  | own => exact .inl rfl
  | pub => exact .inr rfl
  | rgn r => exact absurd hc (hns r u)

theorem tgt_TI {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} {us : List Acc} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some us) : TI η b us pw := by
  obtain ⟨c, U, hsto, hat, hFd, hmo, hini⟩ := ptr_targetM hvars hp ht hea hb
  exact ⟨c, U, μ, hsto, hat, (Fd_accs hFd).trans hacc, hmo, hini, hμ⟩

theorem cell_TI {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hμ : μ = .own ∨ μ = .pub)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : TI η b us pw :=
  tgt_TI hi.2.1 hp (cell_cases hc) hμ hea hb (by
    rw [← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr, hus])

theorem store_TI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : TI η b us pw := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_TI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
        (mode_of_cell hc (hsc _ hp)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_TI hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
        (mode_of_cell hc (hsc _ hp)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, hc⟩ := TermSeenHid.cellOf_of_wordOf hw
      exact cell_TI hi hE htv hp hc (by simp [Cx.opaqueOK, Ty.guardT]) (mode_of_cell hc (hsc _ hp))
        hea hcr hb hus

theorem xchg_TI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : TI η b us pw := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_TI hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
            (mode_of_cell hc (hsc _ hp)) hea hcr hb hus

theorem fetch_TI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : TI η loc [.one] pw := by
  cases hop with
  | fetchCell hp _ hc =>
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_TI hi.2.1 hp (cell_cases hc) (mode_ok (cell_cases hc) ht' hμ') hea hb
          (by simp [cl, accs])
      · exact tgt_TI hi.2.1 hp (cell_cases hc) (mode_ok (cell_cases hc) ht' hμ') hea hb
          (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ : μ = .own ∨ μ = .pub := mode_ok ht ht' hμ'
      exact tgt_TI hi.2.1 hp ht hμ hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ : μ = .own ∨ μ = .pub := mode_ok ht ht' hμ'
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_TI hi.2.1 hp ht hμ hea hb (by simp [cl, accs, hok.1.1.1.1])

theorem cas_mode {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String} {ok fail : Expr} {t u : Ty} {μ : Mode}
    (hsc : StepScope cx (.cas acq rel w e v tn ok fail)) (hp : cx.peek w = .ok t)
    (ht : t = .ptr μ u ∨ t = .loc μ u) : μ = .own ∨ μ = .pub := by
  rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u', ht', -⟩
  · exact mode_ok ht ht' hμ'
  · exact mode_ok ht ht' (.inr rfl)

theorem cas_TI {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : TI η loc [.one] pw := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_TI hi.2.1 hp (cell_cases hc) (cas_mode hsc hp (cell_cases hc)) hea hb (accs_cl_one hraw)
      · exact tgt_TI hi.2.1 hp (cell_cases hc) (cas_mode hsc hp (cell_cases hc)) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_TI hi.2.1 hp ht (cas_mode hsc hp ht) hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_TI hi.2.1 hp ht (cas_mode hsc hp ht) hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      have hμ := cas_mode hsc hp ht
      exact tgt_TI hi.2.1 hp ht hμ hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])

/-! ## The own and pub refutations -/

theorem own_false {η : TEnv} {Eg : GEnv} {i : Nat} {S0 S : AllocLabel → Prop} {a b : Address} {j : Nat}
    {cl c : Cell} {U : Ty} {us : List Acc}
    (hCE : CE η = Cut Eg i S0) (hcl : Eg.sto a.label = some cl) (ho : cl.owner = some i)
    (hPU : PredU (Cut Eg i S) a) (hab : a.label = b.label) (hoff : a.offset = b.offset + j)
    (hsto : η.sto b.label = some c) (hus : accs U = some us) (hini : IniAt (modeIni .own η.ini η.rini) c b U)
    (hj : j < nWords us) : False := by
  obtain ⟨-, -, N, e, us', hty, he, hge⟩ := predU_own hcl ho hPU
  have eS : η.sto = cutSto Eg i := congrArg TEnv.sto hCE
  have eI : η.ini = Eg.ini := congrArg TEnv.ini hCE
  have eR : η.rini = Eg.rini := congrArg TEnv.rini hCE
  have hcc : c = cl := by
    rw [eS, ← hab, cutSto_own hcl ho] at hsto; exact (Option.some.inj hsto).symm
  subst hcc
  have h1 := TermSeenHid.slot_lt hini hus hj N e us' hty he
  have h2 : modeIni .own η.ini η.rini b.label = min (Eg.ini a.label) (Eg.rini a.label) := by
    rw [hab, eI, eR]; rfl
  rw [h2] at h1
  have h1' : @LT.lt Nat _ (b.offset + j) (min (Eg.ini a.label) (Eg.rini a.label) * nWords us') := h1
  have hge' : @LE.le Nat _ (min (Eg.ini a.label) (Eg.rini a.label) * nWords us') a.offset := hge
  have hoff' : @Eq Nat a.offset (b.offset + j) := hoff
  omega

theorem pub_low {g : G} {k : Promises.Knobs} {η : TEnv} {s : St} {Eg : GEnv} {i : Nat}
    {S0 S : AllocLabel → Prop} {a : Address} {cl c : Cell} {pw : Word} {h : Ts}
    (hm : MemInv g (CE η) s) (hCE : CE η = Cut Eg i S0) (hcl : Eg.sto a.label = some cl)
    (ho : cl.owner = some i) (hPU : PredU (Cut Eg i S) a) (hsto : η.sto a.label = some c)
    (hmo : ModeOK η.tid η.pfr η.seen .pub a.label c [pw]) (hvr : pw.view ≤ pw.rts)
    (hhF : ∀ F, Eg.pfr a.label = some F → h ≤ F) : h ≤ TermStoreNI.dep k pw := by
  obtain ⟨hpf, hlt1, N, e, us, hty, he, hge⟩ := predU_own hcl ho hPU
  have eP : η.pfr = Eg.pfr := congrArg TEnv.pfr hCE
  have eI : η.ini = Eg.ini := congrArg TEnv.ini hCE
  have eR : η.rini = Eg.rini := congrArg TEnv.rini hCE
  cases hF : Eg.pfr a.label with
  | none => exact absurd hF hpf
  | some F =>
    have hlt : (CE η).rc a.label < (CE η).ini a.label := by
      show min (η.ini a.label) (η.rini a.label) < η.ini a.label
      rw [eI, eR]
      refine Nat.lt_of_not_le fun hle => ?_
      have h3 : @LT.lt Nat _ a.offset (Eg.ini a.label * nWords us) := hlt1 N e us hty he
      have hge' : @LE.le Nat _ (min (Eg.ini a.label) (Eg.rini a.label) * nWords us) a.offset := hge
      have h4 : Eg.ini a.label * nWords us ≤ min (Eg.ini a.label) (Eg.rini a.label) * nWords us :=
        Nat.mul_le_mul_right _ hle
      omega
    have hP : (CE η).pfr a.label = some F := by show η.pfr a.label = some F; rw [eP]; exact hF
    have hz : ¬ ZW (CE η) a.label := by
      rintro ⟨c2, N2, e2, us2, h1, h2, h3, h4⟩
      have hc2 : (CE η).sto a.label = some cl := by rw [hCE]; exact cutSto_own hcl ho
      rw [hc2] at h1; cases h1
      rw [hty] at h2; simp only [Ty.array.injEq, Idx.lit.injEq] at h2; obtain ⟨-, rfl⟩ := h2
      rw [he] at h3; cases h3
      have h5 := hlt1 N e us hty he
      rw [h4, Nat.mul_zero] at h5
      exact Nat.not_lt_zero _ h5
    exact Nat.le_trans (hhF F hF) (PVc.pv_leaf hm hsto hmo hP hlt hz hvr)

/-! ## `bufInit` -/

theorem bufInit_TI {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) :
    ∃ ad c j rt rti wi, pw.val = .loc ad 0 ∧ b = offs ad (j * nWords us) ∧ evalAt env bb = some (rt, [pw]) ∧
      evalAt env i = some (rti, [wi]) ∧ numOf [wi] = some j ∧ η.sto ad.label = some c ∧
      ∀ N e us', c.ty = .array (.lit N) e → accs e = some us' → ∀ q, q < nWords us →
        @LT.lt Nat _ (ad.offset + j * nWords us + q) ((j + 1) * nWords us') ∨
        @LT.lt Nat _ (ad.offset + j * nWords us + q) (min (η.ini ad.label) (η.rini ad.label) * nWords us') := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, hu', hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, hu', hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', hvb, hlb⟩ := use_FInv hu' hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, hei', hvi, -⟩ := peek_VR hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VR] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, -, hini⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst a0
      simp only [cl, clI_zero] at hat0 hini
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      refine ⟨ad, c, ev ρ jj, _, _, wi, hwv, rfl, hea, hei, hnj, hsto, ?_⟩
      intro N e us' hty he q hq
      have hJn : ev ρ jj < ev ρ n := by omega
      rcases hini N e hty with ⟨hU, h0⟩ | ⟨us0, j1, o, h0, hj1, ho1, hat1⟩
      · rw [hty] at hU
        simp only [Ty.array.injEq, Idx.lit.injEq] at hU
        obtain ⟨-, rfl⟩ := hU
        rw [hacc] at he; cases he
        have h0' : @Eq Nat 0 ad.offset := h0
        left
        rw [Nat.add_mul, Nat.one_mul]; omega
      · rw [he] at h0; cases h0
        have hel := AtOff.elem (n := ev ρ n) hacc hJn (AtOff.here (Or.inl (by simp [hacc])))
        have hb2 := AtOff_bound (AtOff_trans hat1 hel) he hacc
        have hj1' : j1 < min (η.ini ad.label) (η.rini ad.label) := hj1
        have ho1' : @Eq Nat (j1 * nWords us' + o) ad.offset := ho1
        right
        have h2 : (j1 + 1) * nWords us' ≤ min (η.ini ad.label) (η.rini ad.label) * nWords us' :=
          Nat.mul_le_mul_right _ hj1'
        rw [Nat.add_mul, Nat.one_mul] at h2
        omega

/-! ## The theorem -/

theorem ownPredStoreFree_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg}
    (hsc : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (h0 : TermViewInv.ViewInvR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {E' : TEnv}
    (hPH : PredHoldG Eg c)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hF : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hBiO : TermPlant.BiOut th E') :
    ∀ (a : Address) (cl : Cell) (h : Ts), Eg.sto a.label = some cl → cl.owner = some i →
      ¬ Eg.pubd a.label → PredU (Cut Eg i S) a → FirstW c.mem a h → h ∈ th.promises →
      h ∉ r.2.2.promises → IniWr E' a := by
  intro a cl h hcl ho hnp hPU hFW hh hnh
  obtain ⟨S0, ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hFI, hsum, -, hm, -, -⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have hs := hsc X ⟨hCE, htid, hE, hT, htv, hFI, hsum⟩
  have hi := hFI.1
  have eS : η.sto = cutSto Eg i := congrArg TEnv.sto hCE
  have eI : η.ini = Eg.ini := congrArg TEnv.ini hCE
  have eR : η.rini = Eg.rini := congrArg TEnv.rini hCE
  have hhF : ∀ F, Eg.pfr a.label = some F → h ≤ F := by
    obtain ⟨h', hFW', -, hle⟩ := hPH i th S a X.hth ⟨cl, hcl, ho⟩ hnp hPU
    rw [FirstW_uniq hFW hFW']; exact hle
  obtain ⟨-, hful⟩ := TermFul.tstep_fulfil (MemInv_promLt hm) (MemInv_nopair hm) X.hr
  obtain ⟨m, hmt, hsw, -, -⟩ := hful h hh hnh
  obtain ⟨⟨m', hm', hml, -⟩, -⟩ := hFW
  have hmt' : c.mem[h]? = some m := hmt
  rw [hmt'] at hm'
  cases hm'
  rw [hml] at hsw
  have hvr := TermViewInv.envVR_of_run h0 X.run X.hth
  have hE'sto : ∀ c2, E'.sto a.label = some c2 → c2 = cl := by
    intro c2 h2
    rcases hF.2.2.1 a.label with e | ⟨hfr, -⟩
    · rw [e] at h2
      exact Option.some.inj (h2.symm.trans (cutSto_own hcl ho))
    · rw [(X.inv.gfresh X.hth _ a.label hfr).1] at hcl
      cases hcl
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, hee, hev, hb, -⟩
  · rw [hterm] at hT hs
    cases hT.1 with
    | let_ hop _ =>
      rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hloc, -⟩ |
          ⟨o, acq, rel, a', v, t, t', pw, nw, tr, mr, rfl, hea, hev, hb, -⟩
      · have hjl := TermFul.OneAt_lt hj
        subst hloc
        cases op
        case store rl a1 v1 tok =>
          have hsc' : OpScope cx (.store rl a1 v1 tok) := hs.elim id (fun h => h.elim)
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := store_TI hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hle := pub_low (k := k) hm hCE hcl ho hPU hsto hmo
              (hvr _ _ _ pw hea (List.mem_singleton_self _)) hhF
            have hr := X.hr
            rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr
            obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr
            rw [← hreq] at hnh
            simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_map] at hin
            obtain ⟨s'', hs'', he⟩ := hin
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -, -⟩ := he
            exact (hnh (PVc.storeUnits_keepLow hs'' hh (Nat.le_refl _) hle)).elim
        case xchg a1 v1 =>
          have hsc' : OpScope cx (.xchg a1 v1) := hs.elim id (fun h => h.elim)
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := xchg_TI hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hle := pub_low (k := k) hm hCE hcl ho hPU hsto hmo
              (hvr _ _ _ pw hea (List.mem_singleton_self _)) hhF
            have hr := X.hr
            rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr
            obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr
            rw [← hreq] at hnh
            simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_flatMap, List.mem_map] at hin
            obtain ⟨⟨s1, old⟩, hl, s'', hs'', he⟩ := hin
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -, -⟩ := he
            have hk1 := (TermFul.loadUnits_keep us 0 _ _ hl).2.2
            have hh1 : h ∈ s1.promises := by rw [hk1]; exact hh
            exact (hnh (PVc.storeUnits_keepLow hs'' hh1 (Nat.le_refl _) hle)).elim
        case xchgAt =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAt_uaR hop hi hE htv hu
          exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
        case xchgAtF =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAtF_uaR hop hi hE htv hu
          exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
        case stl =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stl_uaR hop hi htv hu
          exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
        case stlw =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stlw_uaR hop hi htv hu
          exact (own_false (b := b) hCE hcl ho hPU rfl rfl hsto hus' hini hjl).elim
        case bufInit bb i1 v1 =>
          obtain ⟨ad, c1, jn, rt, rti, wi, hpw, hbe, hea, hei, hnj, hsto, hbd⟩ := bufInit_TI hop hi hE htv hu
          subst hbe
          intro c2 N e2 us' h2 hty he
          have hc2 := hE'sto c2 h2
          subst hc2
          have hc1 : c1 = c2 := by
            have hcl' : Eg.sto ad.label = some c2 := hcl
            rw [eS, cutSto_own hcl' ho] at hsto; exact (Option.some.inj hsto).symm
          subst hc1
          have hbi : jn < E'.rc ad.label := hBiO x bb i1 v1 e rt pw ad rti wi jn hterm hea hpw hei hnj
          have hI := (hF.2.2.2.2.1 ad.label).1
          have hR := hF.2.2.2.2.2.2.2.2.2.1 ad.label
          have hmin : min (η.ini ad.label) (η.rini ad.label) ≤ min (E'.ini ad.label) (E'.rini ad.label) := by
            rw [eI, eR]
            exact Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) hI, Nat.le_trans (Nat.min_le_right _ _) hR⟩
          have hbi' : jn + 1 ≤ min (E'.ini ad.label) (E'.rini ad.label) := hbi
          show @LT.lt Nat _ (ad.offset + jn * nWords us + j) (min (E'.ini ad.label) (E'.rini ad.label) * nWords us')
          have m1 := Nat.mul_le_mul_right (nWords us') hbi'
          have m2 := Nat.mul_le_mul_right (nWords us') hmin
          rcases hbd N e2 us' hty he j hjl with h1 | h1 <;> omega
        all_goals simp [TermFul.UnitsOp] at hu
      · have hsc' : OpScope cx (.fetch o acq rel a' v) := hs.elim id (fun h => h.elim)
        obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := fetch_TI hop hsc' hi hE htv hm hea hb
        rcases hμ with rfl | rfl
        · exact (own_false (b := a) (j := 0) hCE hcl ho hPU rfl rfl hsto hus' hini (by decide)).elim
        · have hle := pub_low (k := k) hm hCE hcl ho hPU hsto hmo
            (hvr _ _ _ pw hea (List.mem_singleton_self _)) hhF
          have hr := X.hr
          rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr
          obtain ⟨⟨s', t'', ws'⟩, hin, hreq⟩ := hr
          rw [← hreq] at hnh
          simp only [evalOp, hea, hev, hb, List.mem_map] at hin
          obtain ⟨⟨mem', th'⟩, hst, he⟩ := hin
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, -, -⟩ := he
          exact (hnh (PVc.stepRmw_keepLow hst hh (Nat.le_refl _) hle)).elim
  · rw [hterm] at hT hs
    have hsc' : StepScope cx (.cas acq rel w e v tn ok fail) := hs.elim id (fun h => h.elim)
    obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := cas_TI hT.1 hsc' hi hE htv hm hea hb
    rcases hμ with rfl | rfl
    · exact (own_false (b := a) (j := 0) hCE hcl ho hPU rfl rfl hsto hus' hini (by decide)).elim
    · have hle := pub_low (k := k) hm hCE hcl ho hPU hsto hmo
        (hvr _ _ _ pw hea (List.mem_singleton_self _)) hhF
      have hr := X.hr
      simp only [tstep, hterm, hea, hee, hev, hb, List.mem_map] at hr
      obtain ⟨⟨mem', th'⟩, hst, hreq⟩ := hr
      rw [← hreq] at hnh
      exact (hnh (PVc.stepRmw_keepLow (s := stOf c.mem c.pairs th) hst hh (Nat.le_refl _) hle)).elim

#print axioms ownPredStoreFree_of

end TermPredStoreFree
