import WeakCore.TermPoolThread
import WeakCore.TermPoolCovFgn
import WeakCore.TermOverCrPoolG
import WeakCore.TermOwnCF
import WeakCore.TermForWU
import WeakCore.TermULBr
import WeakCore.TermFreeQWP
import WeakCore.TermA4P2

/-! # TermFgnNew: `fgnNew_of`, the F1T `hNew` discharge

At a thread step of `i` and an owned, published, unpublished cell `l` of a foreign thread `j`,
the pre items `Gs` (kept, `K := false`) and the first-write free items `fwL` (at the pre state, zero
resource, pinned by `CrItemQ`'s predicted-unit arm; their pieces are `FreeP` by `SysInv.stoW`, A1) are
post items and cover every post unit (each is `PredU ∧ ¬VisU`, its lowest own promise its first write). -/

namespace TermFgnNew
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermOverCrW TermPoolStaging TermPoolCovFgn TermFreeQW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem map_bitExt_false (Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) :
    Gs.map (bitExt fun _ _ _ => false) = Gs := by
  induction Gs with
  | nil => rfl
  | cons a G ih =>
    rw [List.map_cons, ih]
    simp [bitExt]


/-- **A first-write free item**: `crItemQ_freeG` at a predicted unit whose lowest own promise
`tw` is its first write, pinned to `tw`'s own word. -/
theorem crItemQ_freeFW {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} {b o : Nat}
    {U : Ty} {us : List Acc} {t0 tw : Ts} {mh mq : Msg} {ws : List Word}
    (hmh : s.mem[t0]? = some mh) (hml : mh.loc.label = l) (hlo0 : TermPlant.LowOwn s mh.loc t0)
    (hnw0 : ¬ WordUnit E mh.loc) (hb0 : b ≤ mh.loc.offset) (ho0 : mh.loc.offset < b + nWords us)
    (hat : AtOff c.ty b U) (hsol : Solid U) (hU : accs U = some us) (hb : b ≤ o)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) (hPU : PredU E ⟨l, o⟩) (hfw : FirstW s.mem ⟨l, o⟩ tw)
    (hmq : s.mem[tw]? = some mq)
    (hlen : ws.length = nWords us) (hwo : ws[o - b]? = some (mw mq)) (hv : ValOfR E U ws .zero) :
    TermOverCr.CrItemQ E s cr l c (t0, b, U, ws, .zero, unitK us (o - b)) :=
  crItemQ_freeG hmh hml hlo0 hnw0 hb0 ho0 hat hsol hU hb hsing (fun tw2 hl2 => by
    rw [TermPlant.LowOwn_uniq hl2 hlo]
    exact .inr ⟨hPU, hfw, mq, hmq, rfl⟩) hlen hwo hv

/-- A first-write free item for the own promise `tw`: resource-free, a credited item at every credit,
covering `tw`'s unit. -/
def FwQ (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  x.2.2.2.2.1 = .zero ∧ (∀ cr, TermOverCr.CrItemQ E s cr l c x) ∧ ∃ o, TermPlant.LowOwn s ⟨l, o⟩ tw ∧
    ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧ x.2.2.2.2.2 ii = true

open Classical in
noncomputable def fwIt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  if h : ∃ x, FwQ E s l c tw x then Classical.choose h else (tw, 0, .unit, [], .zero, fun _ => true)

open Classical in
/-- **The first-write free items**: one per own promise with one. -/
noncomputable def fwL (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) :
    List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (s.promises.filter (fun tw => decide (∃ x, FwQ E s l c tw x))).map (fwIt E s l c)

theorem fwIt_spec {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tw : Ts} (h : ∃ x, FwQ E s l c tw x) :
    FwQ E s l c tw (fwIt E s l c tw) := by
  classical
  unfold fwIt
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem mem_fwL {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : x ∈ fwL E s l c) :
    ∃ tw, FwQ E s l c tw x := by
  classical
  unfold fwL at hx
  obtain ⟨tw, htw, rfl⟩ := List.mem_map.1 hx
  exact ⟨tw, fwIt_spec (of_decide_eq_true (List.mem_filter.1 htw).2)⟩

theorem fwL_item {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ fwL E s l c, TermOverCr.CrItemQ E s cr l c x := fun x hx => by
  obtain ⟨tw, -, hi, -⟩ := mem_fwL hx
  exact hi cr

theorem fwL_zero {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} :
    ∀ x ∈ fwL E s l c, x.2.2.2.2.1 = .zero := fun x hx => by
  obtain ⟨tw, hz, -⟩ := mem_fwL hx
  exact hz

theorem fwL_cover {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {tw : Ts}
    (hex : ∃ x, FwQ E s l c tw x) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) :
    ∃ x ∈ fwL E s l c, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧
      x.2.2.2.2.2 ii = true := by
  classical
  have hmem : fwIt E s l c tw ∈ fwL E s l c :=
    List.mem_map.2 ⟨tw, List.mem_filter.2 ⟨hl.1, decide_eq_true hex⟩, rfl⟩
  obtain ⟨-, -, o', hlo', hcv⟩ := fwIt_spec hex
  have eo : o' = o := by
    obtain ⟨m1, hm1, hl1⟩ := hl.2.1
    obtain ⟨m2, hm2, hl2⟩ := hlo'.2.1
    rw [hm1] at hm2
    cases hm2
    exact congrArg Address.offset (hl2.symm.trans hl1)
  subst eo
  exact ⟨_, hmem, hcv⟩

/-- **A first-write free item exists** at an own promise's unit `o` (its unit's only word) in a
`FreeP` piece `U` of a non-word predicted unit whose first write is `tw`, at a typed word. -/
theorem fwQ_exists {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o b : Nat} {U : Ty}
    {us : List Acc} {tw : Ts} {mq : Msg}
    (hsto : E.sto l = some c) (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) (hP : TermPiece.Piece c.ty b U)
    (hU : accs U = some us) (hb : b ≤ o) (ho : o < b + nWords us)
    (hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b)
    (hF : TermA4.FreeP U) (hnw : ¬ WordUnit E ⟨l, o⟩)
    (hPU : PredU E ⟨l, o⟩) (hfw : FirstW s.mem ⟨l, o⟩ tw) (hmq : s.mem[tw]? = some mq)
    (hok : WordOK E c.ty o (mw mq)) :
    ∃ x, FwQ E s l c tw x := by
  obtain ⟨htw, ⟨mw0, hmw, hml⟩, -⟩ := id hl
  obtain ⟨t0, m0, ht0, hm0, hl0, hb0, ho0, -, hmin⟩ := lowest_in_piece (l := l) htw hmw (by rw [hml])
    (by rw [hml]; exact hb) (by rw [hml]; exact ho)
  have hlo0 : TermPlant.LowOwn s m0.loc t0 := ⟨ht0, ⟨m0, hm0, rfl⟩, fun t' m' h1 h2 h3 =>
    hmin t' m' h1 h2 (by rw [h3]; exact hl0) (by rw [h3]; exact hb0) (by rw [h3]; exact ho0)⟩
  have hnw0 : ¬ WordUnit E m0.loc := by
    have e : m0.loc = ⟨l, m0.loc.offset⟩ := by rw [← hl0]
    rw [e]
    exact noWU_piece hsto hP hU hb ho hb0 ho0 hnw
  obtain ⟨ws, hlen, hwo, hv⟩ := valOfR_zero_fillP hok hP.1 hP.2.1 hU hb ho hF
  obtain ⟨ii, hi⟩ := TermPlant.inAcc_ex us (o - b) (by omega)
  exact ⟨_, rfl, fun cr => crItemQ_freeFW hm0 hl0 hlo0 hnw0 hb0 ho0 hP.1 hP.2.1 hU hb hsing hl hPU hfw hmq
    hlen hwo hv, o, hl, us, ii, hU, hb, hi, unitK_of hi⟩

theorem fgnNew_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (_hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0) :
    TermPoolThread.FgnNewT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F crS cr' db' δ Gd X Y Z _ _
    _ _ _
  intro j thj thj' Sj l cl hji hj hj' hc2 hown hpf2 _ Gs _ hit _
  have hj2 : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  have ethj : thj = thj' := Option.some.inj (hj2.symm.trans hj')
  subst ethj
  have Zc := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hgf := gfoot_of X Y Zc
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini2, hrini2, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hpreM := tctx_pre X
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l =
      (Cut Eg j Sj).pfr l := hpfr2
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  have hiniE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l =
      (Cut Eg j Sj).ini l := hini2
  have hrcE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l =
      (Cut Eg j Sj).rc l := by
    show min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
        ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l) = min (Eg.ini l) (Eg.rini l)
    rw [hini2, hrini2]
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  obtain ⟨_, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  have hPUf : ∀ o, PredU (Cut Eg j Sj) ⟨l, o⟩ →
      PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ :=
    fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).2 h
  have hPUb : ∀ o, PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      PredU (Cut Eg j Sj) ⟨l, o⟩ :=
    fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).1 h
  have hPl : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j thj t hj ht
  -- the frame of a pre item (at the pre state) to the post state
  have hfrm : ∀ {cv : Ts → Res} x, TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) cv l cl x →
      cv x.1 ≤ pl j x.1 + δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i x.1 →
      TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
        (stOf c'.mem c'.pairs thj) (fun u => pl j u + δh δ cr pl c c'
          (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i u) l cl x :=
    fun x hx hle => TermOwnCF.crItemQ_frame (s := stOf c.mem c.pairs thj) (s' := stOf c'.mem c'.pairs thj)
      hpreM hPl (fun t h => h) (fun t _ h _ _ => h) hstoE
      (fun S0 ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini)
      (fun o _ _ _ h => hPUf o h) hle hx
  have hlob : ∀ o tw, TermPlant.LowOwn (stOf c'.mem c'.pairs thj) ⟨l, o⟩ tw →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw :=
    fun o tw h => TermOwnCF.lowOwn_backE (s := stOf c.mem c.pairs thj) (s' := stOf c'.mem c'.pairs thj)
      hpreM hPl (fun t h => h) (fun t _ h _ _ => h) h
  have hfwb : ∀ o tw, tw < c.mem.size → FirstW c'.mem ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw :=
    fun o tw htw ⟨⟨m, hm', hl, hu⟩, h2⟩ =>
      ⟨⟨m, by rw [← hpreM tw htw]; exact hm', hl, hu⟩,
        fun t m ht hm0 hl0 => h2 t m ht (by rw [hpreM t (Nat.lt_trans ht htw)]; exact hm0) hl0⟩
  have hT0 : (∃ L, accs cl.ty = some L) ∨ ∃ N e, cl.ty = .array (.lit N) e := by
    rcases hlay with hA | ⟨N, e, he, -⟩
    · exact Or.inl (Option.ne_none_iff_exists'.1 hA)
    · exact Or.inr ⟨N, e, he⟩
  -- every post unit of the cover clause has a first-write free item at the pre state
  have hfw : ∀ o tw, PredU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw →
      ∃ x, FwQ (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl tw x := by
    intro o tw hPU hv hlo hfw0
    obtain ⟨htw, ⟨mq, hmq, hml⟩, -⟩ := id hlo
    have hnw : ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ := fun hw =>
      hv ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoE).2 hw, Vis_pfr hpf2'⟩
    have hok0 := X.inv.promTy j thj tw mq hj htw hmq cl (by rw [hml]; exact hs)
      (by rw [hml]; exact ⟨f, hf⟩)
    rw [hml] at hok0
    have hok : WordOK (Cut Eg j Sj) cl.ty o (mw mq) :=
      WordOK_transferS (InclS_pub_cut Eg j Sj) (X.inv.shty l cl ⟨f, hf⟩ hs) hok0
    obtain ⟨b, U, us, hP, hus, hb, ho⟩ := piece_of_wordOK (X.inv.clo l cl hs) (X.inv.cmg l cl hs) hok0
    have hno := X.inv.promNoTwo j thj tw mq cl hj htw hmq (by rw [hml]; exact hs)
    rw [hml] at hno
    have hsing : ∀ i o2, InAcc us i (o - b) → InAcc us i o2 → o2 = o - b := fun i o2 hio h2 =>
      inAcc_single hP.1 hus hio hT0 (fun q hq => by rw [Nat.add_sub_cancel' hb]; exact hno q hq) o2 h2
    have hF : TermA4.FreeP U := TermA4.freeP_of_pieceT (X.inv.stoW l cl hs) (X.inv.clo l cl hs)
      (X.inv.shty l cl ⟨f, hf⟩ hs) (X.inv.stoNI l cl hs) hpre_c hP hus hb ho hnw
    exact fwQ_exists hpre_c hlo hP hus hb ho hsing hF hnw (hPUb o hPU) hfw0 hmq hok
  refine ⟨fun _ _ _ => false, fwL (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl, ?_, ?_, ?_⟩
  · intro t
    have h0 := sumH_zero (fwL_zero (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) (l := l) (c := cl)) t
    unfold sumH at h0
    rw [h0]
    exact Res.zero_le _
  · rw [map_bitExt_false]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hfrm x (hit x hx) (Res.le_add_right _ _)
    · exact hfrm x (fwL_item (cr := pl j) x hx) (Res.le_add_right _ _)
  · rw [map_bitExt_false]
    intro o tw hPU hv hlo hfw1 _
    have hlo0 := hlob o tw hlo
    obtain ⟨x, hx, rest⟩ := fwL_cover (hfw o tw hPU hv hlo0 (hfwb o tw (hPl tw hlo0.1) hfw1)) hlo0
    exact ⟨x, List.mem_append_right _ hx, rest⟩

#print axioms fgnNew_of

end TermFgnNew
