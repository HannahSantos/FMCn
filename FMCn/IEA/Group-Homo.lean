import FMCn.IEA.Definitions
import FMCn.IEA.Group

theorem Criterion_Resp_Op [Group G] [Group H] (φ : G → H) :
  φ respeita op → φ G-homo :=
by
  intro hop
  have hid : φ respeita id := by
    have h' : (φ has_Id.e) ⋆ (φ has_Id.e) = (φ has_Id.e) := by
      rw [← hop, Monoid.Op_Id]
    exact Op_Only_Id (φ has_Id.e) (has_Id.e : H) ⟨(Idempot_means_id (φ has_Id.e) h'), ⟨Monoid.Op_Id, Monoid.Id_Op⟩⟩
  refine ⟨hop, hid, ?_⟩
  · intro a
    suffices h' : (φ a⁻¹) é o inverso de (φ a) from Cheap_Inv_R (φ a) (φ a⁻¹) h'.2
    refine ⟨?_, ?_⟩
    · rw [← hop, Group.Op_Inv_L, hid]
    · rw [← hop, Group.Op_Inv_R, hid]
