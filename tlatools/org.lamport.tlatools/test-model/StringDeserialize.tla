--------------------------- MODULE StringDeserialize ---------------------------
EXTENDS TLC, IOUtils, FiniteSets

(* Don't let TLC parse this, or it defeats the test.
SerializedSet == {
    "Omnis iusto nisi molestiae consequuntur. Eos ipsum dignissimos rem magnam. Sed nihil amet doloribus facere sequi. Magni omnis voluptatem nam soluta voluptatibus et debitis.",
    "Sunt quas veritatis atque facilis. Vitae qui voluptatibus aut odio. Sequi minima amet ad eum voluptatem vel. Libero maiores aut iusto molestiae accusamus aut ex nihil.",
    "Est dolor earum tempora. Aut ad odio incidunt vero. Eum quia incidunt dolores atque vero distinctio nulla laboriosam.",
    "Atque dolor sequi et et et voluptas quia. Natus voluptas et facere similique aut. Veritatis voluptatem voluptate hic accusamus. Et ullam cum molestiae reiciendis sapiente.",
    "Vitae quia voluptatem tenetur fuga sed. Voluptates delectus porro consequatur ex enim vel. Fuga est autem voluptatem officiis. Maiores dignissimos nobis quibusdam sed sit odit. Incidunt soluta est fugit et incidunt sit ex. Quisquam amet iure eligendi."
}
*)

\* First 2 elems of what's on disk
PartialSet == {
    "Omnis iusto nisi molestiae consequuntur. Eos ipsum dignissimos rem magnam. Sed nihil amet doloribus facere sequi. Magni omnis voluptatem nam soluta voluptatibus et debitis.",
    "Sunt quas veritatis atque facilis. Vitae qui voluptatibus aut odio. Sequi minima amet ad eum voluptatem vel. Libero maiores aut iusto molestiae accusamus aut ex nihil."
}

vosName == TLCGet("-DStringDeserializeTLCTest.vosFileName")

SetOnDisk1 == IODeserialize(vosName, FALSE)
SetOnDisk2 == IODeserialize(vosName, FALSE)

EntireSet == PartialSet \cup SetOnDisk1 \cup SetOnDisk2

ASSUME Cardinality(EntireSet) = 5 \* if this number is bigger, we are making duplicate strings!
ASSUME PartialSet \subseteq SetOnDisk1
ASSUME PartialSet \subseteq SetOnDisk2
ASSUME SetOnDisk1 = SetOnDisk2

=============================================================================

