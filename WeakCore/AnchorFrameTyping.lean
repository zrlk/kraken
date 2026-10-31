import WeakCore.GenLayer
import WeakCore.TermMainPre
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
set_option autoImplicit false
/-! B5 (base): W's thread typing at the anchor gives the ♭ frame typing at a re-related env
`flat η` (rels/rrs replaced by the ♭ relations at the witnesses, so CohBW/CohRB hold by construction).
The return continuation is NOT covered here (`ContB`: see StackLevelZero `contB_f4`). -/
namespace FlatAnchor
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open TermCut TermMain

/-- W `CohR`'s forward half (what the resourceful frame relations denote at their witnesses). -/
def RRSound (η : TEnv) : Prop :=
  (∀ k S ws R, η.rrs k S ws R → VRR (fun _ => 0) (CE η) (η.wit k) S ws R) ∧
  (∀ k S ws R, η.urrs k S ws R → VRR (fun _ => 0) (CE η.unsee) (η.wit k) S ws R)

theorem RRSound.of_CohR {η : TEnv} (hc : CohR η) : RRSound η :=
  ⟨fun k S ws R h => ((hc k).1 _ S ws R).1 h, fun k S ws R h => ((hc k).2 _ S ws R).1 h⟩

theorem RRSound.unsee {η : TEnv} (hR : RRSound η) : RRSound η.unsee := ⟨hR.2, hR.2⟩

theorem RRSound.push0 {η : TEnv} (hR : RRSound η) (s : Ty) : RRSound (η.push0 s) := by
  constructor
  · intro k S ws R h
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
    | succ k => exact hR.1 k S ws R (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)
  · intro k S ws R h
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
    | succ k => exact hR.2 k S ws R (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)

/-- W `VRR` at a pub head is fresh (seen or above the frontier). -/
theorem VRR_pubFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} {R : Res}
    (hp : t.pubHead = true) (h : VRR ρ η t rt ws R) : FreshW η ws := by
  intro a' ha'
  match t, hp, h with
  | .ptr .pub u, _, h =>
    simp only [VRR] at h; obtain ⟨⟨a, c, h1, -, -, -, hm, -⟩, -⟩ := h
    obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
    exact hm
  | .ptrOpt .pub u, _, h =>
    simp only [VRR] at h
    rcases h with ⟨h | ⟨a, c, h1, -, -, -, hm, -⟩, -⟩
    · rw [h] at ha'; simp at ha'
    · obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
      exact hm
  | .loc .pub u, _, h =>
    simp only [VRR] at h
    rcases h with ⟨h | ⟨a, c, U, h1, -, -, -, hm, -⟩, -⟩
    · rw [h.1] at ha'; simp at ha'
    · obtain rfl : a = a' := by have := h1.symm.trans ha'; simpa using this
      exact hm

theorem VRR_pubTopFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} {R : Res}
    (hR : RRSound η) (hp : η.pubTop t = true) (h : VRR ρ η t rt ws R) : FreshW η ws := by
  cases t with
  | tvar k =>
    simp only [VRR] at h
    obtain ⟨w0, h0, h1⟩ := h
    exact FreshW_wle h0 (VRR_pubFresh (η := CE η) hp (hR.1 k rt w0 R h1))
  | _ => refine VRR_pubFresh ?_ h; exact hp

/-- W `VRR` is fresh at every pub position (`pp`, generic over `bx ⊇ η.box` and the oracle;
the `VRR` twin of `VR_ppFresh`). -/
theorem VRR_ppFresh (bx : WeakMem.AllocLabel → Option Box) (t : Ty) : ∀ (PT : Nat → Shp → List Word → Nat → Bool)
    (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word) (R : Res) (i : Nat),
    (∀ l B, η.box l = some B → bx l = some B) →
    (∀ k rt ws i, PT k rt ws i = true → ∀ w0 R, WLe w0 ws → η.rrs k rt w0 R → FreshAt η ws i) →
    VRR ρ η t rt ws R → pp PT bx t rt ws i = true → FreshAt η ws i := by
  induction t with
  | ptr μ u =>
    intro PT ρ η rt ws R i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VRR] at hv
    obtain ⟨⟨a, c, h1, -, -, -, hm, -⟩, -⟩ := hv
    exact FreshAt_head h1 hm i
  | ptrOpt μ u =>
    intro PT ρ η rt ws R i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VRR] at hv
    rcases hv with ⟨hn | ⟨a, c, h1, -, -, -, hm, -⟩, -⟩
    · exact FreshAt_null hn i
    · exact FreshAt_head h1 hm i
  | loc μ u =>
    intro PT ρ η rt ws R i _ _ hv hp
    cases μ <;> simp [pp] at hp
    simp only [VRR] at hv
    rcases hv with ⟨⟨hn, -⟩ | ⟨a, c, U, h1, -, -, -, hm, -⟩, -⟩
    · exact FreshAt_null hn i
    · exact FreshAt_head h1 hm i
  | tid =>
    intro PT ρ η rt ws R i _ _ hv _
    simp only [VRR, VR] at hv
    obtain ⟨⟨l, c, h1, -, -, hm⟩, -⟩ := hv
    exact FreshAt_head h1 hm i
  | refine t ψ ih =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    exact ih PT ρ η rt ws R i hbx hPT hv.1 hp
  | iall b ih =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    exact ih PT (vcons 0 ρ) η rt ws R i hbx hPT (hv 0) hp
  | iex b ih =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    simp only [VRR] at hv
    obtain ⟨n, rb, w, rfl, hv⟩ := hv
    exact ih PT (vcons w ρ) η rb ws R i hbx hPT hv hp
  | tvar k =>
    intro PT ρ η rt ws R i _ hPT hv hp
    simp only [VRR] at hv
    obtain ⟨w0, h0, h1⟩ := hv
    exact hPT k rt ws i hp w0 R h0 h1
  | tex κ b ih =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    simp only [VRR] at hv
    obtain ⟨n, rb, s, rfl, -, -, hv⟩ := hv
    exact ih (shPT PT) ρ (η.push0 s) rb ws R i hbx (fun k rt ws i hq w0 R h0 hr => by
      cases k with
      | zero => simp [shPT] at hq
      | succ k =>
        exact hPT k rt ws i hq w0 R h0 (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr)) hv hp
  | mu b ih =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    simp only [VRR] at hv
    exact ih (shPT PT) ρ (η.push0 (cl ρ η.wit 0 0 (.mu b))) rt ws R i hbx (fun k rt ws i hq w0 R h0 hr => by
      cases k with
      | zero => simp [shPT] at hq
      | succ k =>
        exact hPT k rt ws i hq w0 R h0 (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hr)) hv hp
  | prod a b iha ihb =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    simp only [VRR] at hv
    obtain ⟨ra, rb, rfl, Ra, Rb, -, -, hf⟩ := hv
    cases hn : ra.wc with
    | none => simp [pp, hn] at hp
    | some n =>
      obtain ⟨-, h1, h2⟩ := hf n hn
      simp only [pp, hn] at hp
      by_cases hi : i < n
      · simp only [hi, if_true] at hp
        have := iha PT ρ η ra (ws.take n) Ra i hbx hPT h1 hp
        intro w a' g hw hv'
        exact this w a' g (by rw [List.getElem?_take]; simp [hi, hw]) hv'
      · simp only [hi, if_false] at hp
        have := ihb PT ρ η rb (ws.drop n) Rb (i - n) hbx hPT h2 hp
        intro w a' g hw hv'
        exact this w a' g (by rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega)]; exact hw) hv'
  | sum a b iha ihb =>
    intro PT ρ η rt ws R i hbx hPT hv hp
    simp only [VRR] at hv
    obtain ⟨n, Ra, Rb, rfl, hc⟩ := hv
    rcases hc with ⟨htier, x, s, B, h1, -, h3, rfl, -, -, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · simp only [pp, htier, if_true, h1, hbx _ _ h3] at hp
      by_cases hlt : B.tag - s < (armsOf Ra).length
      · simp only [hlt, if_true] at hp
        by_cases hbr : isBoxed Ra = true
        · simp only [hbr, if_true] at hp
          exact iha PT ρ η _ ws R i hbx hPT ((hA hlt).1 hbr) hp
        · simp [hbr] at hp
      · simp only [hlt, if_false] at hp
        by_cases hbr : isBoxed Rb = true
        · simp only [hbr, if_true] at hp
          exact ihb PT ρ η _ ws R i hbx hPT ((hB (by omega)).1 hbr) hp
        · simp [hbr] at hp
    · have htb : (Ty.sum Ra Rb).tier ≠ .boxed := by
        intro h; rw [h] at hd; simp [decodeArm] at hd
      simp only [pp, htb, if_false, hd] at hp
      by_cases hp0 : p = []
      · simp [hp0] at hp
      simp only [hp0, if_false] at hp
      by_cases hj : j < (armsOf Ra).length
      · simp only [hj, if_true] at hp
        obtain ⟨q, hq, hvq⟩ := hA hj
        simp only [hq] at hp
        have hf := iha PT ρ η _ q R _ hbx hPT hvq hp
        intro w a' g hw hv'
        obtain ⟨w', g', hw', hv1, he1⟩ := dec_corr hd hp0 i w a' g hw hv'
        obtain ⟨w'', g'', hw'', hv2, he2⟩ := ofArm_corr hq _ w' a' g' hw' hv1
        obtain ⟨f, hf1, hf2⟩ := hf w'' a' g'' hw'' hv2
        exact ⟨f, hf1, by rw [he2, he1] at hf2; exact hf2⟩
      · simp only [hj, if_false] at hp
        obtain ⟨q, hq, hvq⟩ := hB (by omega)
        simp only [hq] at hp
        have hf := ihb PT ρ η _ q R _ hbx hPT hvq hp
        intro w a' g hw hv'
        obtain ⟨w', g', hw', hv1, he1⟩ := dec_corr hd hp0 i w a' g hw hv'
        obtain ⟨w'', g'', hw'', hv2, he2⟩ := ofArm_corr hq _ w' a' g' hw' hv1
        obtain ⟨f, hf1, hf2⟩ := hf w'' a' g'' hw'' hv2
        exact ⟨f, hf1, by rw [he2, he1] at hf2; exact hf2⟩
  | _ => intro PT ρ η rt ws R i _ _ _ hp; simp [pp] at hp

/-- W `VRR` at a `PubPosE` position is fresh (RRSound feeds the tvar oracle). -/
theorem VRR_PubPosEFresh {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} {R : Res}
    (hR : RRSound η) (hp : PubPosE η t rt ws) (h : VRR ρ η t rt ws R) : FreshW η ws := by
  obtain ⟨bx, hbx, hp⟩ := hp
  refine FreshW_of_at0 (VRR_ppFresh bx t (PTopB bx η) ρ η rt ws R 0 hbx ?_ h hp)
  intro k rt' ws' i hq w0 R' h0 hr
  have hv := VRR_up (η.wit k) rt' w0 ws' R' h0 (hR.1 k rt' w0 R' hr)
  exact VRR_ppFresh bx (η.wit k) (fun _ _ _ _ => false) (fun _ => 0) (CE η) rt' ws' R' i
    hbx (fun _ _ _ _ h => by simp at h) hv hq

/-- W `VRR` embeds in ♭ `VRRB` at the same env. -/
theorem VRR_VRRB0 (t : Ty) : ∀ (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word) (R : Res),
    RelsSound η → RRSound η → VRR ρ η t rt ws R → VRRB ρ η t rt ws R := by
  induction t with
  | tid =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    exact ⟨VR_VRB hR h.1, h.2⟩
  | opq o =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    exact ⟨VR_VRB hR h.1, h.2⟩
  | refine t ψ ih =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    exact ⟨ih _ _ _ _ _ hR hRR h.1, h.2, fun hp => Or.inl (VRR_PubPosEFresh hRR hp h.1)⟩
  | iex b ih =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, rb, w, hrt, hv⟩ := h; exact ⟨n, rb, w, hrt, ih _ _ _ _ _ hR hRR hv⟩
  | prod a b iha ihb =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨ra, rb, hrt, Ra, Rb, hRab, hz, hf⟩ := h
    exact ⟨ra, rb, hrt, Ra, Rb, hRab, hz, fun n hn =>
      ⟨(hf n hn).1, iha _ _ _ _ _ hR hRR (hf n hn).2.1, ihb _ _ _ _ _ hR hRR (hf n hn).2.2⟩⟩
  | sum a b iha ihb =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h
    refine ⟨n, Ra, Rb, hrt, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · refine Or.inl ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, fun hl => ⟨fun hb => iha _ _ _ _ _ hR hRR ((hA hl).1 hb),
        fun hb => ?_⟩, fun hl => ⟨fun hb => ihb _ _ _ _ _ hR hRR ((hB hl).1 hb), fun hb => ?_⟩⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hb
        exact ⟨q, q1, q2, q3, q4, iha _ _ _ _ _ hR.unsee hRR.unsee q5⟩
      · obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl).2 hb
        exact ⟨q, q1, q2, q3, q4, ihb _ _ _ _ _ hR.unsee hRR.unsee q5⟩
    · refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj; exact ⟨q, q1, iha _ _ _ _ _ hR hRR q2⟩
      · obtain ⟨q, q1, q2⟩ := hB hj; exact ⟨q, q1, ihb _ _ _ _ _ hR hRR q2⟩
  | ptr μ u _ =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨⟨a, c, h1, h2, h3, h4, hm, h5⟩, hR'⟩ := h
    exact ⟨⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩, hR'⟩
  | ptrOpt μ u _ =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨h | ⟨a, c, h1, h2, h3, h4, hm, h5⟩, hR'⟩ := h
    · exact ⟨Or.inl h, hR'⟩
    · exact ⟨Or.inr ⟨a, c, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩, hR'⟩
  | loc μ u _ =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨h | ⟨a, c, U, h1, h2, h3, h4, hm, h5⟩, hR'⟩ := h
    · exact ⟨Or.inl h, hR'⟩
    · exact ⟨Or.inr ⟨a, c, U, h1, h2, h3, h4, ModeOK_b _ hm, h5⟩, hR'⟩
  | tex κ b ih =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h
    exact ⟨n, rb, s, hrt, hc, hw, ih _ _ _ _ _ (hR.push0 s) (hRR.push0 s) hv⟩
  | mu b ih =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    exact ih _ _ _ _ _ (hR.push0 _) (hRR.push0 _) h
  | iall b ih =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    exact fun n => ih _ _ _ _ _ hR hRR (h n)
  | tvar k =>
    intro ρ η rt ws R hR hRR h; simp only [VRR] at h; simp only [VRRB]
    obtain ⟨ws', h1, h2⟩ := h; exact ⟨ws', h1, Or.inl h2⟩
  | _ =>
    intro ρ η rt ws R hR hRR h
    (try simp only [VRR] at h) <;> (try simp only [VRRB]) <;> exact h

/-! ## The re-related env -/

/-- `η` with its frame relations replaced by the ♭ relations at the witnesses. -/
def flat (η : TEnv) : TEnv :=
  { η with
    rels := fun k S ws => (VRF False) (fun _ => 0) (CE η) (η.wit k) S ws
    urels := fun k S ws => (VRF False) (fun _ => 0) (CE η.unsee) (η.wit k) S ws
    rrs := fun k S ws R => VRRB (fun _ => 0) (CE η) (η.wit k) S ws R
    urrs := fun k S ws R => VRRB (fun _ => 0) (CE η.unsee) (η.wit k) S ws R }

theorem CE_flat (η : TEnv) : CE (flat η) = CE η := rfl
theorem CE_flat_unsee (η : TEnv) : CE (flat η).unsee = CE η.unsee := rfl

theorem EnvOKB_flat {p : Prog} {η : TEnv} (hE : EnvOK p η) : EnvOKB p (flat η) := by
  refine ⟨hE.1, fun k => ⟨(hE.2.1 k).1, fun ρ' S ws => ?_, fun ρ' S ws => ?_⟩, fun k => ⟨fun ρ' S ws X => ?_,
    fun ρ' S ws X => ?_⟩⟩
  · exact VR_cloB (hE.2.1 k).1 _ _ S ws
  · exact VR_cloB (η := η.unsee) (hE.2.1 k).1 _ _ S ws
  · exact VRR_cloB (hE.2.1 k).1 _ _ S ws X
  · exact VRR_cloB (η := η.unsee) (hE.2.1 k).1 _ _ S ws X

theorem RelsSound_CE (η : TEnv) : RelsSound (CE η) :=
  ⟨fun _ _ _ h => by simp [CE] at h, fun _ _ _ h => by simp [CE, TEnv.unsee] at h⟩

theorem RRSound_CE (η : TEnv) : RRSound (CE η) :=
  ⟨fun _ _ _ _ h => by simp [CE] at h, fun _ _ _ _ h => by simp [CE, TEnv.unsee] at h⟩

/-- W `VR` at `η` is ♭ `VRF False` at `flat η`. -/
theorem VR_flat {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word}
    (h : VR ρ η t rt ws) : (VRF False) ρ (flat η) t rt ws :=
  VR_monoB t η (flat η) ρ rt ws
    (fun k S vs hk => VR_VRB (RelsSound_CE η) (((hc k).2.1 _ S vs).1 hk))
    (fun k S vs hk => VR_VRB (RelsSound_CE η.unsee) (((hc k).2.2 _ S vs).1 hk))
    rfl rfl rfl (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h)
    (VR_VRB (RelsSound.of_Coh hc) h) (fun _ => Nat.le_refl _)

/-- W `VRR` at `η` is ♭ `VRRB` at `flat η`. -/
theorem VRR_flat {η : TEnv} (hc : Coh η) (hr : CohR η) {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word}
    {R : Res} (h : VRR ρ η t rt ws R) : VRRB ρ (flat η) t rt ws R :=
  VRR_monoB t η (flat η) ρ rt ws R
    (fun k S vs Y hk => VRR_VRRB0 _ _ _ _ _ _ (RelsSound_CE η) (RRSound_CE η) (((hr k).1 _ S vs Y).1 hk))
    (fun k S vs Y hk => VRR_VRRB0 _ _ _ _ _ _ (RelsSound_CE η.unsee) (RRSound_CE η.unsee)
      (((hr k).2 _ S vs Y).1 hk))
    rfl rfl rfl (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h) (fun _ _ h => h)
    (VRR_VRRB0 _ _ _ _ _ _ (RelsSound.of_Coh hc) (RRSound.of_CohR hr) h) (fun _ => Nat.le_refl _)

theorem VarsOKB_flat {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {σs : List Ty} {vars : List (String × Ty × Bool)}
    {env : Env} (h : VarsOK ρ η σs vars env) : VarsOKB ρ (flat η) σs vars env := fun x e he => by
  obtain ⟨rt, ws, h1, h2, h3⟩ := h x e he
  exact ⟨rt, ws, h1, VR_flat hc h2, h3⟩

theorem HeldOKB_flat {η : TEnv} (hc : Coh η) (hr : CohR η) {ρ : Nat → Nat} {cx : Cx} {env : Env} {Rf : Res}
    (h : HeldOK ρ η cx env Rf) : HeldOKB ρ (flat η) cx env Rf := by
  obtain ⟨h1, h2, h3, Rx, h4, h5⟩ := h
  refine ⟨h1, h2, h3, Rx, fun x e he hh => ?_, h5⟩
  obtain ⟨rt, ws, q1, q2⟩ := h4 x e he hh
  exact ⟨rt, ws, q1, VRR_flat hc hr q2⟩

theorem FInvB_flat {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} (h : FInv ρ η σs K cx env) : FInvB glb gnum gi ρ (flat η) σs (fun _ _ => True) cx env := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, VarsOKB_flat hc h2, fun _ _ _ _ _ _ => trivial, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ## Memory half: W's MemInv / MemHeld at `CE η` embed in the ♭ families (words at `CE`, no frame relations) -/
section mem
variable {η : TEnv}

theorem ValOf_B {T : Ty} {ws : List Word} (h : ValOf η T ws) : ValOfB η T ws := by
  unfold ValOf at h; unfold ValOfB; exact ⟨VR_VRB (RelsSound_CE _) h.1, h.2⟩
theorem ValOfR_B {T : Ty} {ws : List Word} {R : Res} (h : ValOfR η T ws R) : ValOfRB η T ws R := by
  unfold ValOfR at h; unfold ValOfRB
  exact ⟨VRR_VRRB0 _ _ _ _ _ _ (RelsSound_CE _) (RRSound_CE _) h.1, h.2⟩
theorem ValOfS_B {T : Ty} {ws : List Word} (h : ValOfS η T ws) : ValOfSB η T ws := by
  unfold ValOfS at h; unfold ValOfSB; exact ⟨ValOf_B h.1, h.2⟩
theorem WordOK_B {T : Ty} {o : Nat} {w : Word} (h : WordOK η T o w) : WordOKB η T o w := by
  unfold WordOK at h; unfold WordOKB
  obtain ⟨b, S, ws, o', w0, h1, h2, h3, h4, h5⟩ := h; exact ⟨b, S, ws, o', w0, h1, ValOfS_B h2, h3, h4, h5⟩
theorem PairOK_B {T : Ty} {o : Nat} {w0 w1 : Word} (h : PairOK η T o w0 w1) : PairOKB η T o w0 w1 := by
  unfold PairOK at h; unfold PairOKB
  obtain ⟨b, S, ws, o', x0, x1, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨b, S, ws, o', x0, x1, h1, ValOfS_B h2, h3, h4, h5, h6, h7⟩
theorem BufOK_B {n : Nat} {T : Ty} {vals : List Word} (h : BufOK η n T vals) : BufOKB η n T vals := by
  unfold BufOK at h; unfold BufOKB
  obtain ⟨N, e, us, h1, h2, h3, h4, h5⟩ := h; exact ⟨N, e, us, h1, h2, h3, h4, fun j hj => ValOf_B (h5 j hj)⟩
theorem CellOK_B {n : Nat} {T : Ty} {vals : List Word} (h : CellOK η n T vals) : CellOKB η n T vals := by
  unfold CellOK at h; unfold CellOKB; exact h.imp (And.imp_right ValOf_B) BufOK_B
theorem BufOKR_B {n nr : Nat} {T : Ty} {vals : List Word} {R : Res} (h : BufOKR η n nr T vals R) :
    BufOKRB η n nr T vals R := by
  unfold BufOKR at h; unfold BufOKRB
  obtain ⟨N, e, us, Rs, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨N, e, us, Rs, h1, h2, h3, h4, h5, h6, fun j Rj hj hR =>
    ⟨(h7 j Rj hj hR).1, fun q => ValOfR_B ((h7 j Rj hj hR).2 q)⟩⟩
theorem CellOKR_B {n nr : Nat} {T : Ty} {vals : List Word} {R : Res} (h : CellOKR η n nr T vals R) :
    CellOKRB η n nr T vals R := by
  unfold CellOKR at h; unfold CellOKRB; exact h.imp (And.imp_right ValOfR_B) BufOKR_B
theorem HiddenP_B {T : Ty} {mem : Memory} {P : List Ts} {l : AllocLabel} {o : Nat} {V : Ts}
    (h : HiddenP η T mem P l o V) : HiddenPB η T mem P l o V := by
  unfold HiddenP at h; unfold HiddenPB
  exact fun t m h1 h2 h3 hn => h t m h1 h2 h3 (fun hw => hn (WordOK_B hw))
theorem MemOKP_B {mem : Memory} {pairs P : List Ts} (h : MemOKP η mem pairs P) : MemOKPB η mem pairs P := by
  unfold MemOKP at h; unfold MemOKPB
  exact ⟨fun t m c a b d => (h.1 t m c a b d).imp id WordOK_B,
    fun t m0 m1 c a b d e => PairOK_B (h.2.1 t m0 m1 c a b d e), h.2.2⟩
theorem OwnHidP_B {mem : Memory} {vs : VState} {P : List Ts} (h : OwnHidP η mem vs P) : OwnHidPB η mem vs P := by
  unfold OwnHidP at h; unfold OwnHidPB
  refine ⟨fun l c a b o hi => HiddenP_B (h.1 l c a b o hi), fun l c a b d => ?_⟩
  obtain ⟨f, hf, hs, hh⟩ := h.2 l c a b d
  exact ⟨f, hf, hs, fun o hi => HiddenP_B (hh o hi)⟩
theorem PubDefP_B {mem : Memory} {P : List Ts} (h : PubDefP η mem P) : PubDefPB η mem P := by
  unfold PubDefP at h; unfold PubDefPB
  exact fun l c f a b d o hi => HiddenP_B (h l c f a b d o hi)
theorem Inh_B (h : Inh η) : InhB η := by
  unfold Inh at h; unfold InhB
  intro l c b S us a b' d e
  obtain ⟨ws, hw, hl⟩ := h l c b S us a b' d e
  exact ⟨ws, ValOf_B hw, hl⟩
theorem segTearB {T S : Ty} {b : Nat} (hc : Ty.coupledOKIn [] T = true) (hs : SegOf T b S) : TearOKB S := by
  rcases hs with ⟨-, rfl, -⟩ | ⟨N, us, j, rfl, -, -, -⟩
  · exact TearOK_of_cplB hc
  · simp only [Ty.coupledOKIn] at hc; exact TearOK_of_cplB hc
theorem PubCpl_B (h : PubCpl η) : PubCplB η := by
  unfold PubCpl at h; unfold PubCplB
  intro l c f a b
  obtain ⟨h1, -, h3, h4, h5⟩ := h l c f a b
  exact ⟨h1, fun b S hs _ => segTearB h3 hs, h3, h4, h5⟩
theorem PubPair_B {mem : Memory} {pairs P : List Ts} (h : PubPair η mem pairs P) : PubPairB η mem pairs P := by
  unfold PubPair at h; unfold PubPairB
  intro l c f o a b d e t0 t1 m0 m1 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact PairOK_B (h l c f o a b d e t0 t1 m0 m1 q1 q2 q3 q4 q5 q6 q7 q8 q9)
theorem PubMem_B {mem : Memory} {pairs P : List Ts} (h : PubMem η mem pairs P) : PubMemB η mem pairs P := by
  unfold PubMem at h; unfold PubMemB; exact ⟨PubPair_B h.1, h.2⟩
theorem PubInv_B {s : St} (h : PubInv η s) : PubInvB η s := by
  unfold PubInv at h; unfold PubInvB; exact ⟨h.1, Inh_B h.2.1, PubCpl_B h.2.2.1, PubMem_B h.2.2.2⟩
theorem TypedAt_B {c : Cell} {m : Msg} (h : TypedAt η c m) : TypedAtB η c m := by
  unfold TypedAt at h; unfold TypedAtB; exact WordOK_B h
theorem LatestSF_B {c : Cell} {fr : Option Ts} {mem : Memory} {S : Ts → Prop} {coh : Address → Ts} {a : Address}
    {w : Word} (h : LatestSF η c fr mem S coh a w) : LatestSFB η c fr mem S coh a w := by
  unfold LatestSF at h; unfold LatestSFB
  obtain ⟨⟨m, h1, h2, h3⟩, h4, h5⟩ := h
  exact ⟨⟨m, h1, h2, h3.imp id (And.imp_right TypedAt_B)⟩, h4,
    fun t m a b d => (h5 t m a b d).imp id (And.imp_right TypedAt_B)⟩
theorem OwnPairF_B {c : Cell} {l : AllocLabel} {vals : List Word} {mem : Memory} {pairs : List Ts}
    {S : Ts → Prop} {coh : Address → Ts} (h : OwnPairF η c l vals mem pairs S coh) :
    OwnPairFB η c l vals mem pairs S coh := by
  unfold OwnPairF at h; unfold OwnPairFB
  intro o a b t0 t1 m0 m1 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact (h o a b t0 t1 m0 m1 q1 q2 q3 q4 q5 q6 q7 q8 q9).imp id PairOK_B
theorem OwnOKSF_B {mem : Memory} {pairs : List Ts} {vs : VState} {S : Ts → Prop} (h : OwnOKSF η mem pairs vs S) :
    OwnOKSFB η mem pairs vs S := by
  unfold OwnOKSF at h; unfold OwnOKSFB
  intro l c a b
  obtain ⟨vals, h1, h2, h3⟩ := h l c a b
  exact ⟨vals, CellOK_B h1, fun o v hv => LatestSF_B (h2 o v hv), fun hp => OwnPairF_B (h3 hp)⟩
/-- `hri`: the rini clause of the (iii) `FreshLP` (♭ `FreshLPA`);
at a `SysInvN` base it is `rle` + the FreshLP ini = 0 (`base_shape`). -/
theorem MemInv_B {g : G} {s : St} (h : MemInv g η s) : MemInvB g η s := by
  unfold MemInv at h; unfold MemInvB
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨MemOKP_B h1, OwnOKSF_B h2, h3,
    h4, h5, OwnHidP_B h6, PubDefP_B h7, h8, PubInv_B h9, h10, h11⟩
theorem MemHeld_B {s : St} {H : Res} (h : MemHeld η s H) : MemHeldB η s H := by
  unfold MemHeld at h; unfold MemHeldB
  obtain ⟨L, Rl, h1, h2, h3, h4⟩ := h
  refine ⟨L, Rl, h1, h2, h3, fun l hl => ⟨(h4 l hl).1, fun c hc => ?_⟩⟩
  obtain ⟨vals, q1, q2⟩ := (h4 l hl).2 c hc
  exact ⟨vals, q1, CellOKR_B q2⟩
end mem

/-- The return continuation in ♭ form (`ContB`), stated at the anchor env `E` only. -/
def ContB (lb n i : Nat) (p : Prog) (th : TTh) (E : TEnv) : Prop :=
  ∀ (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rs : Res), CE η = E → EnvOK p η →
    (∃ N, ∀ k, N ≤ k → Rs (.own (freshLabel lb n i k)) = 0) →
    RetOKR ρ η th.σs cx.ret (ResumeR p th.stack Rs) → RetOKRB lb n i ρ (flat η) th.σs cx.ret (ResumeRB lb n i p th.stack Rs)

/-- **B5**: `ThSysAt` at the anchor gives the ♭ thread invariant at the same cut, given `ContB`. -/
theorem base_shape {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} {S : AllocLabel → Prop} (hclo : GStoClo Eg)
    (h : ThSysAt p g mem pairs th Eg Tot HP HS cr db S) (hK : ContB g.lbase g.n g.i p th (Cut Eg g.i S))
    (hRs : ∀ Rf Rs : Res, Rf + Rs = Tot → ∃ N, ∀ k, N ≤ k → Rs (.own (freshLabel g.lbase g.n g.i k)) = 0)
    (hrle : ∀ l, Eg.rini l ≤ Eg.ini l) :
    ThInvREB g.lbase g.n g.i p (Cut Eg g.i S) th Tot ∧ MemInvB g (Cut Eg g.i S) (stOf mem pairs th) ∧
      MemHeldB (Cut Eg g.i S) (stOf mem pairs th) (HP + HS) := by
  obtain ⟨-, η0, -, -, -, hCE0, -, -, -, -, -, -, -, hm, hH, -, -⟩ := ThSysAt.env hclo h
  obtain ⟨⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩, -⟩ := h
  refine ⟨⟨ρ, flat η, cx, Rf, Rs, by rw [CE_flat]; exact hCE, EnvOKB_flat hE, hT, htv,
    ⟨FInvB_flat hE.2.1 hi.1, hK ρ η cx Rs hCE hE (hRs Rf Rs hsum) hi.2.1, HeldOKB_flat hE.2.1 hE.2.2 hi.2.2⟩, hsum, hpw⟩, ?_, ?_⟩
  · have hr0 : ∀ l, η0.rini l ≤ η0.ini l := fun l => by
      have h1 : η0.rini l = Eg.rini l := congrArg (fun e => TEnv.rini e l) hCE0
      have h2 : η0.ini l = Eg.ini l := congrArg (fun e => TEnv.ini e l) hCE0
      rw [h1, h2]; exact hrle l
    rw [← hCE0]
    exact MemInv_B hm
  · rw [← hCE0]; exact MemHeld_B hH

/-- (CONTB D1) At a `SysInvN` base, any split `Rf + Rs = Tot i` leaves no `own` key of `i`'s unborn labels
in `Rs` (W `SysInvN.ownF` = `OwnFreshZ`, `N := th.nalloc`): `base_shape`'s `hRs`. -/
theorem rsFresh_of {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    (hinv : TermMain.SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[i]? = some th) :
    ∀ Rf Rs : Res, Rf + Rs = Tot i → ∃ N, ∀ j, N ≤ j → Rs (.own (freshLabel c.lbase c.n i j)) = 0 := by
  intro Rf Rs hsum
  refine ⟨th.nalloc, fun j hj => ?_⟩
  have hz := (hinv.ownF i th j hth hj).1 i (TermCert.arr_lt hth)
  simp only [Res.add_apply] at hz
  rw [← hsum] at hz
  simp only [Res.add_apply] at hz
  omega

/-- **B4 (L4 at ♭)**: every thread state of a Solo window into a certified configuration has the `PromAbove`
result hypothesis that the ♭ step lemmas (`tstepMR_*B`, `tstepMCF_stepB`) take. -/
theorem b4_promAbove {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c1 : Cfg} {th : TTh}
    (hs : Solo p k arch i c c1) (hc : Certified p k arch c1 i) (hth : c.ths[i]? = some th) :
    PromAbove (stOf c.mem c.pairs th) :=
  fun t ht m hm => TermCert.certified_promAbove (TermCert.certified_of_solo hs hc) hth ht hm

end FlatAnchor
