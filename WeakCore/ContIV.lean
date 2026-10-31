import WeakCore.StackResFree
import WeakCore.EtaL
/-! **ContIV**: `ContE` at a window anchor from W's `MemInv` there, through
`contE_f4` (StackResFree) at the thread's own plan `planAt c1.lbase c1.n i …`.
* `freshSup_of_supI`: the supply `SupI` gives `FreshSup` at a plan of the same geometry.
* `tailBlank_of_memInv`: W `MemInv` gives `TailBlank` at that plan (the rini clause is read from W's `FreshLP`
  inside `MemInv`; no extra hypothesis).
* `resumeBs_supI`: the resource-free local mirror at `SupI`: `ResumeBs (SupI lb n i) = ResumeB lb n i`.
* `contE_of`: `ContE c1.lbase c1.n i p th1 (CE η)` (replaces the window temporary `WinTmpA.contE`). -/
namespace ContAnchor
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep CertWinProof TermCut TermCert
open TermSound.Flat TermMem.Flat TermStep.Flat
open WeakMem (Msg Memory Address Ts)

/-- (2) **Bridge**: the supply gives `FreshSup` at a plan with the same geometry. -/
theorem freshSup_of_supI {P : Plan} {lb n i : Nat} {η : TEnv} (h : SupI lb n i η)
    (hb : P.base = lb) (hn : P.n = n) (hi : P.i = i) : ∃ b, FreshSup P b η := by
  obtain ⟨b, hB, hpay⟩ := h
  have tl : ∀ l, P.Tail b l → ∃ k, b ≤ k ∧ l = freshLabel lb n i k := by
    rintro l ⟨k, hk, rfl⟩; exact ⟨k, hk, by unfold Plan.fl; rw [hb, hn, hi]⟩
  refine ⟨b, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).1
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).2.1
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).2.2.1
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).2.2.2.1
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).2.2.2.2.1
  · intro l ht; obtain ⟨k, hk, rfl⟩ := tl l ht; exact (hB k hk).2.2.2.2.2
  · intro x B hx w hw a g hv ht
    obtain ⟨k, hk, e⟩ := tl _ ht
    exact hpay x B hx w hw a g hv k hk e

/-- (1) **TailBlank from MemInv** at a plan of the thread's geometry with `nalloc ≤ N5`
(the rini clause is read from W's `FreshLP` inside `MemInv`). -/
theorem tailBlank_of_memInv {g : G} {E : TEnv} {s : St} (hm : MemInv g E s)
    {M N5 : Nat} (hn : 0 < g.n) (hM : 0 < M) (stack : List Frame) (hN : s.nalloc ≤ N5) :
    TailBlank (planAt g.lbase g.n g.i M N5 hn hM stack) E := by
  obtain ⟨-, -, -, ⟨hF, -⟩, hS, -, -, -, -, ⟨hB, -, -⟩, -⟩ := hm
  rintro m ⟨k, hk, rfl⟩
  have e : (planAt g.lbase g.n g.i M N5 hn hM stack).fl k = freshLabel g.lbase g.n g.i k := rfl
  rw [e]
  have hk1 : s.nalloc ≤ k :=
    Nat.le_trans hN (Nat.le_trans (planAt_ok g.lbase g.n g.i M N5 hn hM stack).1 hk)
  refine ⟨(hF k hk1).1, hB k hk1, (hF k hk1).2.2.1, (hF k hk1).2.2.2.1, (hF k hk1).2.2.2.2, fun hsn => ?_⟩
  obtain ⟨f, hf, -⟩ := hS _ hsn
  rw [(hF k hk1).2.2.2.2] at hf; cases hf

/-- (resource-free mirror) At `Sup := SupI lb n i` the local mirror `ResumeBs` is the ♭ `ResumeB`. -/
theorem resumeBs_supI {lb n i : Nat} {p : Prog} :
    ∀ st : List Frame, ResumeBs (SupI lb n i) lb n i p st = ResumeB lb n i p st
  | [] => by funext E ws; simp [ResumeBs, ResumeB]
  | f :: rest => by
      funext E ws
      simp only [ResumeBs, ResumeB, FInvBs, FInvB, RetOKBs, RetOKB, resumeBs_supI rest]

/-- (3) **contE at a window anchor** `c1` (thread `i`, `th1`, adversarial typing `CE η`), from W's `MemInv` there
and the rini clause read from W's `FreshLP` inside `MemInv`. -/
theorem contE_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c1 : Cfg} {th1 : TTh} {η : TEnv}
    (hth1 : c1.ths[i]? = some th1) (hm : MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1)) :
    ContE c1.lbase c1.n i p th1 (CE η) := by
  have hn : 0 < (gOf p k arch c1 i).n := Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth1))
  have hM : 0 < 3 * (th1.stack.length + 1) := by omega
  intro ρ' η' cx' hCE hE hK
  have h := contE_f4 (glb := c1.lbase) (gnum := c1.n) (gi := i) (Sup := SupI c1.lbase c1.n i)
    (P := planAt c1.lbase c1.n i (3 * (th1.stack.length + 1)) th1.nalloc hn hM th1.stack)
    (fun _ h => freshSup_of_supI h rfl rfl rfl) (Nat.le_refl _)
    (planAt_ok c1.lbase c1.n i _ th1.nalloc hn hM th1.stack).2
    (tailBlank_of_memInv (g := gOf p k arch c1 i) hm hn hM th1.stack (Nat.le_refl _)) ρ' η' cx' hCE hE hK
  rw [resumeBs_supI] at h
  exact h

/-- (resource mirror) At `Sup := SupI lb n i` the local mirror `ResumeRBs` is the ♭ `ResumeRB`. -/
theorem resumeRBs_supI {lb n i : Nat} {p : Prog} :
    ∀ st : List Frame, ResumeRBs (SupI lb n i) lb n i p st = ResumeRB lb n i p st
  | [] => by funext Rs E rd ws R; simp [ResumeRBs, ResumeRB]
  | f :: rest => by
      funext Rs E rd ws R
      simp only [ResumeRBs, ResumeRB, FInvRBs, FInvRB, RetOKRBs, RetOKRB, resumeRBs_supI rest]

/-- (4) **contB at a `SysInvN` base** from the thread's `MemInv` at the cut and W `rle`, via `contB_f4` at the plan
`planAt lb n i … (max nalloc N)` chosen AFTER `Rs` (its D1 witness `N` sets the plan start, so `RsSup` holds by
`RsSup_of`). No temporary: rini on the cut's fresh labels is `rle` + FreshLP ini = 0. -/
theorem contB_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c : Cfg} {th : TTh} {Eg : GEnv}
    {S : WeakMem.AllocLabel → Prop}
    (hth : c.ths[i]? = some th) (hm : MemInv (gOf p k arch c i) (Cut Eg i S) (stOf c.mem c.pairs th))
    (hrle : ∀ l, Eg.rini l ≤ Eg.ini l) :
    FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S) := by
  have hn : 0 < (gOf p k arch c i).n := Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))
  have hM : 0 < 3 * (th.stack.length + 1) := by omega
  intro ρ η cx Rs hCE hE hRsN hK
  obtain ⟨N, hN⟩ := hRsN
  let P := planAt c.lbase c.n i (3 * (th.stack.length + 1)) (max th.nalloc N) hn hM th.stack
  have hok := planAt_ok c.lbase c.n i (3 * (th.stack.length + 1)) (max th.nalloc N) hn hM th.stack
  have hRs : RsSup P Rs := fun l ⟨kk, hk, e⟩ => by
    rw [e]; exact hN kk (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hok.1 hk))
  have h := contB_f4 (glb := c.lbase) (gnum := c.n) (gi := i) (Sup := SupI c.lbase c.n i) (P := P)
    (fun _ h => freshSup_of_supI h rfl rfl rfl) (Nat.le_refl _) hok.2
    (tailBlank_of_memInv (g := gOf p k arch c i) hm hn hM th.stack (Nat.le_max_left _ _)) ρ η cx Rs hCE hE hRs hK
  rw [resumeRBs_supI] at h
  exact h

end ContAnchor
