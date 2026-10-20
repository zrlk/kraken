import WeakCore.TermTyped
import WeakCore.TermPlant
import WeakCore.TermMainDefs

/-! # TermRiniCoh: the (i′ seed) clause `riniCoh` and its preservation (not installed)

* (now in `TermTyped`) `riniSlot_of`: `PrivCoh` + `RiniCoh` give the ungated `RiniMem` body (every own buffer, seen or not,
  with or without a frontier) at `E1 = E`; so `RiniPl E E E s` and `RiniMem E E s` at a run start;
* `riniCoh_init`: empty memory;
* `riniCoh_gfoot`: an idle thread under another thread's step;
* `riniCoh_prom`: a promise step (with or without a plant);
* `riniCoh_step`: the stepper (publish, alloc, free, store/xchg/cas through `WrSiteA` + strict frontier,
  `bufInit` through `BiOut`).
Strict frontier bound `hlt` (`f < mem.size`): `FrontierLt`.
-/

namespace TermRiniCoh
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermMain
open TermTyped (RiniCoh)

/-- The strict frontier, needed only at own positive-width array cells (at size 0 the
plain `FrontierLe … (size - 1)` gives nothing; `memPos_of_own` gives `0 < size` exactly here). -/
def HltOwn (sto : AllocLabel → Option Cell) (pfr : AllocLabel → Option Ts) (i n : Nat) : Prop :=
  ∀ l cl f N e us, sto l = some cl → cl.owner = some i → pfr l = some f → cl.ty = .array (.lit N) e →
    accs e = some us → 0 < N * nWords us → f < n

/-- `RiniCoh` at a cut does not depend on the cut's seen set. -/
theorem riniCoh_seen {Eg : GEnv} {i : Nat} {S S' : AllocLabel → Prop} {s : St}
    (h : RiniCoh (Cut Eg i S) s) : RiniCoh (Cut Eg i S') s := h

/-- At an empty memory `RiniCoh` is vacuous. -/
theorem riniCoh_empty {E : TEnv} {s : St} (h : s.mem = #[]) : RiniCoh E s := by
  intro t m _ _ _ _ _ _ hm
  rw [h] at hm
  simp at hm

/-- **The initial configuration** (empty memory): the clause at every thread and cut. -/
theorem riniCoh_init {c : Cfg} {Eg : GEnv} (hmem : c.mem = #[]) :
    ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th → RiniCoh (Cut Eg i S) (stOf c.mem c.pairs th) :=
  fun _ _ _ _ => riniCoh_empty (s := stOf _ _ _) hmem

/-- **An idle thread across another thread's step** (`GFoot`): its cells, owners and frontiers are
the same, its promises unchanged, its counts only grow; messages at or below an old frontier are old
(strict frontier bound `hlt`). -/
theorem riniCoh_gfoot {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg2 n n' v)
    {j : Nat} (hj : j ≠ g.i) (fp : Nat → List Ts) {S S' : AllocLabel → Prop} {s s' : St}
    (hlt : HltOwn Eg.sto Eg.pfr j s.mem.size)
    (hP : s'.promises = s.promises) (hmem : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (h : RiniCoh (Cut Eg j S) s) : RiniCoh (Cut (Eg2.withFp fp) j S') s' := by
  intro t m c N e us f ht hm hc hown hpf htf hty hus h1 h2
  have hc2 : Eg2.sto m.loc.label = some c := cutSto_sub hc
  have hown' : c.owner = some j := hown
  have hc0 : Eg.sto m.loc.label = some c := by
    rcases hf.2.1 m.loc.label with e | ⟨-, -, -, T, hT⟩
    · rw [← e]; exact hc2
    · rw [hT] at hc2; cases hc2; exact absurd (Option.some.inj hown').symm hj
  have hpf2 : Eg2.pfr m.loc.label = some f := hpf
  have hpf0 : Eg.pfr m.loc.label = some f := by
    rcases hf.2.2.2.2.1 m.loc.label with e | ⟨-, f', -, -, c', hc', ho'⟩ | ⟨-, -, e⟩
    · rw [← e]; exact hpf2
    · rw [hc0] at hc'; cases hc'; rw [hown'] at ho'; exact absurd (Option.some.inj ho') hj
    · rw [e] at hc2; cases hc2
  have hrc : (Cut Eg j S).rc m.loc.label ≤ (Cut (Eg2.withFp fp) j S').rc m.loc.label := by
    have a := (hf.2.2.2.1 m.loc.label).1
    have b := hf.2.2.2.2.2.1 m.loc.label
    show min (Eg.ini _) (Eg.rini _) ≤ min (Eg2.ini _) (Eg2.rini _)
    omega
  have htl : t < s.mem.size := Nat.lt_of_le_of_lt htf (hlt _ c f N e us hc0 hown' hpf0 hty hus (Nat.lt_of_le_of_lt (Nat.zero_le _) h2))
  have hm0 : s.mem[t]? = some m := by rw [← hmem t htl]; exact hm
  have ht0 : t ∉ s.promises := by rw [← hP]; exact ht
  exact h t m c N e us f ht0 hm0 (cutSto_own hc0 hown') hown hpf0 htf hty hus
    (Nat.le_trans (Nat.mul_le_mul_right _ hrc) h1) h2

/-- **A promise step** of `j` with plant `P` (`EgP = (plantG Eg P N).withFp _`): cells kept, counts
only grow, old frontiers kept; a newly planted label is a pfr-none own cell of `j` (`PlantSpec`), at
which the pre-state `PrivCoh` covers every old non-promise message, and the one new message is `j`'s
own new promise. -/
theorem riniCoh_prom {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {i j : Nat}
    (fp : Nat → List Ts) {S S' : AllocLabel → Prop} {s s' : St}
    (hlt : HltOwn Eg.sto Eg.pfr i s.mem.size)
    (hPS : ∀ l f, P l = some f → Eg.pfr l = none ∧ Eg.OwnAt j l ∧ f ≤ s.mem.size)
    (hsub : ∀ t, t ∈ s.promises → t ∈ s'.promises)
    (hmem : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hsz : s'.mem.size = s.mem.size + 1)
    (hnew : i = j → s.mem.size ∈ s'.promises)
    (hpc : PrivCoh (Cut Eg i S) s) (h : RiniCoh (Cut Eg i S) s) :
    RiniCoh (Cut ((plantG Eg P N).withFp fp) i S') s' := by
  intro t m c N' e us f ht hm hc hown hpf htf hty hus h1 h2
  have hc0 : Eg.sto m.loc.label = some c := cutSto_sub (Eg := (plantG Eg P N).withFp fp) hc
  have hown' : c.owner = some i := hown
  have hini : Eg.ini m.loc.label ≤ (plantG Eg P N).ini m.loc.label := by
    simp only [plantG]; split <;> omega
  have hrc : (Cut Eg i S).rc m.loc.label ≤ (Cut ((plantG Eg P N).withFp fp) i S').rc m.loc.label := by
    show min (Eg.ini _) (Eg.rini _) ≤ min ((plantG Eg P N).ini _) (Eg.rini _)
    omega
  have hlo : (Cut Eg i S).rc m.loc.label * nWords us ≤ m.loc.offset :=
    Nat.le_trans (Nat.mul_le_mul_right _ hrc) h1
  have hpf' : (plantG Eg P N).pfr m.loc.label = some f := hpf
  have hold : t < s.mem.size → t ∉ s.promises ∧ s.mem[t]? = some m := fun htl =>
    ⟨fun h' => ht (hsub t h'), by rw [← hmem t htl]; exact hm⟩
  cases hq : P m.loc.label with
  | none =>
    have hpf0 : Eg.pfr m.loc.label = some f := by
      simp only [plantG, hq] at hpf'; exact hpf'
    obtain ⟨ht0, hm0⟩ := hold (Nat.lt_of_le_of_lt htf (hlt _ c f N' e us hc0 hown' hpf0 hty hus (Nat.lt_of_le_of_lt (Nat.zero_le _) h2)))
    exact h t m c N' e us f ht0 hm0 (cutSto_own hc0 hown') hown hpf0 htf hty hus hlo h2
  | some f' =>
    obtain ⟨hpn, ⟨c', hc', ho'⟩, -⟩ := hPS _ f' hq
    rw [hc0] at hc'
    cases hc'
    have hij : i = j := by rw [hown'] at ho'; exact Option.some.inj ho'
    rcases Nat.lt_or_ge t s.mem.size with htl | htl
    · obtain ⟨ht0, hm0⟩ := hold htl
      exact (hpc t m ht0 hm0 ⟨c, N', e, us, cutSto_own hc0 hown', hown, hpn, hty, hus, hlo, h2⟩).2
    · have hts : t < s'.mem.size := by
        rcases Nat.lt_or_ge t s'.mem.size with h3 | h3
        · exact h3
        · rw [Array.getElem?_eq_none_iff.2 h3] at hm; cases hm
      have htt : t = s.mem.size := by omega
      exact absurd (htt ▸ hnew hij) ht

/-- **The stepper**, at the step's witness `E'` (`EFoot`): an old non-promise message is covered by
the pre-state clause (old frontier) or `PrivCoh` (new frontier: a publish); a fresh label has no
frontier; a write at an initialised unit is below `rc` (`InitRr`; a pfr-none own cell has `ini ≤ rini`,
`iniLe_of_hid`; a seen non-zero-width own cell likewise, `OwnHidP.2`), above the frontier, or a fresh
append above it (strict frontier `hlt`); a `bufInit` write is below the post count (`BiOut`). -/
theorem riniCoh_step {g : G} {E E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh}
    (hm : MemInv g E (stOf mem pairs th))
    (hF : EFoot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hW : TermTyped.WrSiteA g E mem pairs th r)
    (hB : TermPlant.BiOut th E')
    (hlt : HltOwn E.sto E.pfr E.tid mem.size)
    (h : RiniCoh E (stOf mem pairs th)) : RiniCoh E' (stOf r.1 r.2.1 r.2.2) := by
  intro t m c N e us f ht hm' hc hown hpf htf hty hus h1 h2
  have hfrN : ¬ FreshIn g th.nalloc r.2.2.nalloc m.loc.label := by
    rintro ⟨q, hq1, hq2, hql⟩
    have hz := hm.2.2.2.1.1 q hq1
    rw [← hql] at hz
    rcases hF.2.2.2.2.2.1 m.loc.label with e | ⟨-, F, -, -, -, ⟨c', hc', -⟩, -⟩ | ⟨-, -, e⟩
    · rw [e, hz.2.2.2] at hpf; cases hpf
    · rw [hz.1] at hc'; cases hc'
    · rw [e] at hc; cases hc
  have hc0 : E.sto m.loc.label = some c := by
    rcases hF.2.2.1 m.loc.label with e | ⟨hfr, -⟩
    · rw [← e]; exact hc
    · exact absurd hfr hfrN
  have hown0 : c.owner = some E.tid := by rw [← hF.2.1]; exact hown
  have hpf0 : E.pfr m.loc.label = some f ∨ E.pfr m.loc.label = none := by
    rcases hF.2.2.2.2.2.1 m.loc.label with e | ⟨hn, -⟩ | ⟨-, -, e⟩
    · rw [← e]; exact .inl hpf
    · exact .inr hn
    · rw [e] at hc; cases hc
  have hrc : E.rc m.loc.label ≤ E'.rc m.loc.label := by
    have a := (hF.2.2.2.2.1 m.loc.label).1
    have b := hF.2.2.2.2.2.2.2.2.2.1 m.loc.label
    unfold TEnv.rc
    omega
  have hlo : E.rc m.loc.label * nWords us ≤ m.loc.offset := Nat.le_trans (Nat.mul_le_mul_right _ hrc) h1
  rcases hW t m ht hm' with ⟨ht0, hm0⟩ | hfr | ⟨c1, hc1, hI, hI2⟩ |
      ⟨x, bb, ib, v, e', hterm, rt, w, ad, rti, wi, n, c1, hea, hw, hei, hn, hl, hc1, hlt1⟩
  · rcases hpf0 with hp | hp
    · exact h t m c N e us f ht0 hm0 hc0 hown0 hp htf hty hus hlo h2
    · exact (hm.2.2.2.1.2 t m ht0 hm0 ⟨c, N, e, us, hc0, hown0, hp, hty, hus, hlo, h2⟩).2
  · exact absurd hfr hfrN
  · rw [hc0] at hc1
    cases hc1
    have hIo := hI N e us hty hus
    have hcon : E.ini m.loc.label ≤ E.rc m.loc.label → False := fun hle =>
      absurd (Nat.lt_of_lt_of_le hIo (Nat.mul_le_mul_right _ hle)) (Nat.not_lt.2 hlo)
    rcases hpf0 with hp | hp
    · rcases hI2 with hr | hs | hft | hseen
      · exact absurd (hr N e us hty hus) (Nat.not_lt.2 hlo)
      · exact absurd (Nat.lt_of_le_of_lt htf (hlt _ c f N e us hc0 hown0 hp hty hus (Nat.lt_of_le_of_lt (Nat.zero_le _) h2))) (Nat.not_lt.2 hs)
      · exact absurd (hft f hp) (Nat.not_lt.2 htf)
      · by_cases hlt2 : E.rc m.loc.label < E.ini m.loc.label
        · obtain ⟨-, -, hz, -⟩ := hm.2.2.2.2.2.1.2 _ c hc0 hown0 hlt2
          by_cases hzw : ZW E m.loc.label
          · obtain ⟨c2, N2, e2, us2, hc2, hty2, hus2, h0⟩ := hzw
            rw [hc0] at hc2
            cases hc2
            rw [hty] at hty2
            cases hty2
            rw [hus] at hus2
            cases hus2
            rw [h0, Nat.mul_zero] at h2
            exact absurd h2 (Nat.not_lt_zero _)
          · exact absurd hseen (hz hzw)
        · exact (hcon (Nat.le_of_not_lt hlt2)).elim
    · have hle := TermTyped.iniLe_of_hid hm.2.2.2.2.2.1 hc0 hown0 hp
      exact (hcon (by unfold TEnv.rc; omega)).elim
  · have hb := hB x bb ib v e' rt w ad rti wi n hterm hea hw hei hn
    rw [hl] at hb
    rw [hc0] at hc1
    cases hc1
    have h3 := hlt1 N e us hty hus
    exact absurd (Nat.lt_of_lt_of_le h3 (Nat.mul_le_mul_right _ hb)) (Nat.not_lt.2 h1)

theorem hltOwn_of_frlt {sto : AllocLabel → Option Cell} {pfr : AllocLabel → Option Ts} {i n : Nat}
    (hfr : ∀ l cl f, sto l = some cl → pfr l = some f → f ≤ n - 1)
    (hpos : ∀ l cl N e us, sto l = some cl → cl.owner = some i → cl.ty = .array (.lit N) e →
      accs e = some us → 0 < N * nWords us → 0 < n) :
    TermRiniCoh.HltOwn sto pfr i n :=
  fun l cl f N e us hs ho hp hty hus hw =>
    Nat.lt_of_le_of_lt (hfr l cl f hs hp) (Nat.sub_lt (hpos l cl N e us hs ho hty hus hw) Nat.one_pos)

theorem hltOwn_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {n : Nat}
    (h : TermRiniCoh.HltOwn Eg.sto Eg.pfr i n) :
    TermRiniCoh.HltOwn (Cut Eg i S).sto (Cut Eg i S).pfr (Cut Eg i S).tid n :=
  fun l cl f N e us hs ho hp => h l cl f N e us (cutSto_sub (Eg := Eg) hs) ho hp

/-- `PrivCoh` at a cut does not depend on the cut's seen set. -/
theorem privCoh_seen {Eg : GEnv} {i : Nat} {S S' : AllocLabel → Prop} {s : St}
    (h : PrivCoh (Cut Eg i S) s) : PrivCoh (Cut Eg i S') s := h

/-- `HltOwn` at thread `j` from its `MemInv` and `frlt` (the `memPos_of_own` gives `0 < size`). -/
theorem hltOwn_of_cut {g : G} {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {s : St}
    (hm : MemInv g (Cut Eg j S) s) (hfr : FrontierLe Eg (s.mem.size - 1)) :
    TermRiniCoh.HltOwn Eg.sto Eg.pfr j s.mem.size :=
  hltOwn_of_frlt hfr fun l cl N e us hs ho hty hus hw => by
    have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, Nat.zero_mul] at hw; exact Nat.lt_irrefl _ hw
    have hu : 0 < nWords us := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, Nat.mul_zero] at hw; exact Nat.lt_irrefl _ hw
    exact TermTyped.memPos_of_own (E := Cut Eg j S) hm (cutSto_own hs ho) ho hty hus hu hN

/-- `HltOwn` at every thread of a `SysInvN` configuration (`thr`'s `MemInv` + `frlt`). -/
theorem hltOwn_sys {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {thj : TTh} (hj : c.ths[j]? = some thj) :
    TermRiniCoh.HltOwn Eg.sto Eg.pfr j c.mem.size := by
  obtain ⟨S, -, -, hm, -⟩ := h.thr j thj hj
  exact hltOwn_of_cut hm h.frlt

/-- `PrivCoh` at every thread of a `SysInvN` configuration, at any seen set. -/
theorem privCoh_sys {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {thj : TTh} (hj : c.ths[j]? = some thj)
    (S' : AllocLabel → Prop) : PrivCoh (Cut Eg j S') (stOf c.mem c.pairs thj) := by
  obtain ⟨S, -, -, hm, -⟩ := h.thr j thj hj
  exact privCoh_seen hm.2.2.2.1.2

end TermRiniCoh

#print axioms TermRiniCoh.riniCoh_seen
#print axioms TermRiniCoh.riniCoh_init
#print axioms TermRiniCoh.riniCoh_gfoot
#print axioms TermRiniCoh.riniCoh_prom
#print axioms TermRiniCoh.riniCoh_step
#print axioms TermRiniCoh.hltOwn_of_frlt
#print axioms TermRiniCoh.hltOwn_cut
#print axioms TermRiniCoh.privCoh_seen
#print axioms TermRiniCoh.hltOwn_of_cut
#print axioms TermRiniCoh.hltOwn_sys
#print axioms TermRiniCoh.privCoh_sys
