import WeakCore.TermB5

/-!
# TermAnch (certWin-D, F1): the typed write-location fact

`wrIniC : WrIniC` — a typed, in-scope thread step's non-promise result messages are old
non-promise messages, at fresh labels, at initialised units (`InitR`), or in the slot range of
the buffer a `bufInit` writes (`WrSite`).  Old promises it fulfils: `TermFul.tstep_fulfil` +
`TermPlantF.SWIni`; new messages: `TermB5.tstep_newR` + the `IniAt` unit lemmas of
`TermPlantF`; `bufInit`: `TermB5.bufInit_inv`.
-/

namespace TermAnch

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `TermPlantF.unitsAtI_initR` at any word of the units. -/
theorem unitsAtI_initRn {η : TEnv} {b : Address} {us : List Acc} {j : Nat} (h : TermPlantF.UnitsAtI η b us)
    (hjl : j < nWords us) : ∃ c, η.sto b.label = some c ∧ InitR η c b.label (b.offset + j) := by
  obtain ⟨c, U, hsto, hat, hus, hini⟩ := h
  refine ⟨c, hsto, fun N e use hT huse => ?_⟩
  rcases hini N e hT with ⟨rfl, -⟩ | ⟨use', jj, o, huse', hjj, ho, hato⟩
  · rw [hT] at hus; simp [accs] at hus
  · rw [huse] at huse'; cases huse'
    obtain ⟨pre, post, e1, e2⟩ := AtOff_embed hato huse hus
    have hn : nWords use = nWords pre + nWords us + nWords post := by
      rw [e1, nWords_append, nWords_append]
    have hm : (jj + 1) * nWords use ≤ η.ini b.label * nWords use := Nat.mul_le_mul_right _ hjj
    rw [Nat.succ_mul] at hm
    omega

/-- `TermB5.pair_uaI` with `IniAt` only (`TermPlantF.UnitsAtI`). -/
theorem pair_uaIP {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) : TermPlantF.UnitsAtI η b [.two] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := TermPlantF.ptr_targetI hvars hp ht hea hb
  refine ⟨c, U, hsto, hat, (Fd_accs hFd).trans ?_, hini⟩
  rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [cl, accs]

theorem stp_uaIP {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty} {pw : Word}
    {b : Address} (hop : OpT p cx x (.stp rel a v0 v1 tk) c') (hsc : OpScope cx (.stp rel a v0 v1 tk))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env a = some (t, [pw])) (hb : addrOf pw = some b) :
    TermPlantF.UnitsAtI η b [.two] := by
  have hp : ∃ t, cx.peek a = .ok t := by cases hop <;> exact ⟨_, ‹_›⟩
  obtain ⟨t', hp⟩ := hp
  obtain ⟨μ, r, P, ht, -⟩ := hsc t' hp
  exact pair_uaIP hi.2.1 hp ht (.inl ⟨r, P, rfl⟩) hea hb

theorem casp_uaIP {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    {tw : Ty} {pw : Word} {A : Address}
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hsc : StepScope cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env w = some (tw, [pw])) (hb : addrOf pw = some A) :
    TermPlantF.UnitsAtI η A [.two] := by
  have hp : ∃ t, cx.peek w = .ok t := by cases hT <;> exact ⟨_, ‹_›⟩
  obtain ⟨t, hp⟩ := hp
  obtain ⟨μ, u, ht, -, hu⟩ := hsc t hp
  exact pair_uaIP hi.2.1 hp ht hu hea hb

/-- The slot of a buffer component (`IniAt`, at offset `ad.offset`): word `j` of slot `jv` lies
below slot `jv + 1` of the cell. -/
theorem bufInit_slot {ini : AllocLabel → Nat} {c : Cell} {ad : Address} {N jv j : Nat} {U : Ty}
    {us : List Acc} (hini : IniAt ini c ad (.array (.lit N) U)) (hat : AtOff c.ty ad.offset (.array (.lit N) U))
    (hus : accs U = some us) (hj : j < nWords us) :
    ∀ N' el us', c.ty = .array (.lit N') el → accs el = some us' →
      ad.offset + (jv * nWords us + j) < (jv + 1) * nWords us' := by
  intro N' el us' hT he
  have h1 := AtOff_arr_here hat hT (by rw [he]; simp) (by simp [accs])
  rw [hT] at h1
  simp only [Ty.array.injEq, Idx.lit.injEq] at h1
  obtain ⟨-, hU⟩ := h1
  rw [← hU, hus] at he; cases he
  rcases hini N' el hT with ⟨-, h0⟩ | ⟨us2, j2, o, he2, -, -, hato⟩
  · rw [← h0, Nat.succ_mul, Nat.zero_add]; exact Nat.add_lt_add_left hj _
  · exact absurd (by simp [accs] : accs (Ty.array (.lit N) U) = none) (accs_AtOff hato (by rw [he2]; simp))

/-- A typed `bufInit`'s written word `j` is a `WrSite` slot word. -/
theorem bufInit_site {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb ib v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {j : Nat}
    (hop : OpT p cx x (.bufInit bb ib v) c') (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb ib v) pw b rel us ws) (hj : j < nWords us) :
    ∃ rt w ad rti wi n c, evalAt env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧
      evalAt env ib = some (rti, [wi]) ∧ numOf [wi] = some n ∧ ad.label = (offs b j).label ∧
      η.sto (offs b j).label = some c ∧
      ∀ N el us', c.ty = .array (.lit N) el → accs el = some us' → (offs b j).offset < (n + 1) * nWords us' := by
  obtain ⟨rt, rti, wi, ad, c, N, U, jv, hea, hw, hei, hn, hb, hsto, -, hini, hat, -, hus⟩ :=
    TermB5.bufInit_inv hop hi hE htv hu
  subst hb
  refine ⟨rt, pw, ad, rti, wi, jv, c, hea, hw, hei, hn, rfl, hsto, fun N' el us' hT he => ?_⟩
  have := bufInit_slot (jv := jv) hini hat hus hj N' el us' hT he
  simpa [offs, Nat.add_assoc] using this

/-- A capability step appends nothing at a `NewR` position. -/
theorem newR_cap {g : G} {env : Env} {s : St} {op : Op} {b : Address} {us : List Acc} {x : String} {e : Expr}
    {t : Expr} (hc : CapT t) (ht : t = .let_ x op e) (h : TermB5.OpNewR g env s op b us) : False := by
  obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := hc <;> rw [he] at ht <;> cases ht <;>
  rcases h with ⟨_, _, _, hu⟩ | ⟨_, _, _, _, _, _, _, hop, -⟩ | ⟨_, _, _, _, _, _, _, hop, -⟩ <;>
  first | (simp [TermFul.UnitsOp] at hu) | cases hop

/-- **The typed write-location fact.** -/
theorem wrSite_ok {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hr : r ∈ tstep g mem pairs th) : WrSite g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLt hm) (MemInv_nopair hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      rcases TermPlantF.SWIni hE hT htv hi hm (TermTyped.scopeD_SW hsc hsw) hsw with h | ⟨x, bb, ib, v, e, hterm⟩
      · exact .inr (.inr (.inl h))
      · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
        rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
        · rw [hterm] at hterm'
          simp only [Expr.let_.injEq] at hterm'
          obtain ⟨rfl, rfl, rfl⟩ := hterm'
          rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
          · have hT' := hT
            rw [hterm] at hT'
            cases hT' with
            | let_ hop _ => rw [hl]; exact bufInit_site (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
          · cases hop'
        · rw [hterm] at hterm'; cases hterm'
    · exact .inl ⟨htp, hm1⟩
  · rcases TermB5.tstep_newR (MemInv_promLt hm) hr t m (by omega) hmt with hf | hn
    · exact .inr (.inl hf)
    rcases hn with ⟨x, op, e, hterm, b, us, j, hon, hl, hrole⟩ |
        ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
        ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩
    · have hjl := TermB5.roleR_lt hrole
      have hss : StepScope cx th.term := hsc.elim id fun h => (newR_cap h.2 hterm hon).elim
      rw [hterm] at hT hss
      cases hT with
      | let_ hop _ =>
          rcases hon with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
              ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
          · rcases TermPlantF.unitsOp_uaI hop hss hi hE htv hu with hU | ⟨bb, ib, v, rfl⟩
            · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hU hjl
              exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
            · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
              rw [hl]; exact bufInit_site (η := η) hop hi hE htv hu hjl
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (stp_uaIP hop hss hi hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.fetch_swI hop hss hi hE htv hm hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.cas_swI hT hss hi hE htv hm hea hb)
        (show 0 < nWords [Acc.one] by decide)
      have e0 : m.loc = offs m.loc 0 := (TermStepper.offs_zero _).symm
      exact .inr (.inr (.inl ⟨c, hc, by rw [e0]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      have hua := casp_uaIP hT hss hi hea hb
      rcases hl with ⟨hl, -⟩ | ⟨hl, -⟩
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 0 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 0 := by rw [hl, TermStepper.offs_zero]
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 1 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 1 := hl
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))

end TermAnch

#print axioms TermAnch.wrSite_ok
