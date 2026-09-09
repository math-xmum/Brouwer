import Gametheory.Brouwer
import Gametheory.Brouwer_product
import Gametheory.Nash
import Gametheory.Primitive
import Gametheory.Scarf
import Gametheory.ScarfPath
import Gametheory.Simplex

/-!
# Axiom audit

Building this module prints the axioms used by the principal paper endpoints.
It belongs to the default umbrella import, so `lake build` checks the complete
artifact and reruns this audit.
-/

#print axioms IndexedLOrder.internal_door_two_rooms
#print axioms IndexedLOrder.odd_card_filter_isColorful
#print axioms IndexedLOrder.Scarf
#print axioms ScarfPath.component_structure
#print axioms Primitive.isRoomPrimitive_iff_isPrimitive
#print axioms Primitive.isAlmostPrimitive_iff_native
#print axioms Primitive.Trace.nonempty
#print axioms Primitive.Coordinate.exists_model
#print axioms Primitive.Coordinate.IsPrimitive.erase_replacement
#print axioms size_bound_in
#print axioms size_bound_out
#print axioms Brouwer
#print axioms project_embed_id
#print axioms Brouwer_Product
#print axioms FinGame.mixed_g_linear
#print axioms ExistsNashEq
