"""Positive and fail-closed examples for generic dictionary certification."""

PREFIX = """open Aeneas Aeneas.Std
namespace GenericContractProbe

def dictionary {T State : Type} (child : NyxSszRust.codec.Ssz T State) :
    NyxSszRust.codec.Ssz T State := child

def counted {T State : Type} (_count : Usize) (child : NyxSszRust.codec.Ssz T State) :
    NyxSszRust.codec.Ssz T State := child
"""

POSITIVE = """
theorem lawful {T State : Type} (child : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : NyxSszVerification.CodecLaw child shape observe) :
    NyxSszVerification.CodecLaw (dictionary child) shape observe := law

theorem countedLawful {T State : Type} (count : Usize)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : NyxSszVerification.CodecLaw child shape observe) :
    NyxSszVerification.CodecLaw (counted count child) shape observe := law
end GenericContractProbe
check_trait_contract GenericContractProbe.dictionary against NyxSszVerification.CodecLaw
  via GenericContractProbe.lawful
check_trait_contract GenericContractProbe.counted against NyxSszVerification.CodecLaw
  via GenericContractProbe.countedLawful
"""

NEGATIVE = {
    "EmptyGenericDomain": ("""
theorem restricted {T State : Type} (_impossible : Fin 0)
    (child : NyxSszRust.codec.Ssz T State) (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : NyxSszVerification.CodecLaw child shape observe) :
    NyxSszVerification.CodecLaw (dictionary child) shape observe := law
end GenericContractProbe
check_trait_contract GenericContractProbe.dictionary against NyxSszVerification.CodecLaw
  via GenericContractProbe.restricted
""", "unused or constrained"),
    "SpecializedGenericBound": ("""
theorem restricted {T State : Type} (child : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : NyxSszVerification.CodecLaw child shape observe) :
    NyxSszVerification.CodecLaw (counted 0#usize child) shape observe := law
end GenericContractProbe
check_trait_contract GenericContractProbe.counted against NyxSszVerification.CodecLaw
  via GenericContractProbe.restricted
""", "distinct universal parameters"),
    "SpecializedChildShape": ("""
theorem restricted {T State : Type} (child : NyxSszRust.codec.Ssz T State)
    (observe : T → Ssz.Value) (law : NyxSszVerification.CodecLaw child .bool observe) :
    NyxSszVerification.CodecLaw (dictionary child) .bool observe := law
end GenericContractProbe
check_trait_contract GenericContractProbe.dictionary against NyxSszVerification.CodecLaw
  via GenericContractProbe.restricted
""", "independent universal parameters"),
    "AssumedParentLaw": ("""
theorem restricted {T State : Type} (child : NyxSszRust.codec.Ssz T State)
    (shape : Ssz.Desc) (observe : T → Ssz.Value)
    (law : NyxSszVerification.CodecLaw (dictionary child) shape observe) :
    NyxSszVerification.CodecLaw (dictionary child) shape observe := law
end GenericContractProbe
check_trait_contract GenericContractProbe.dictionary against NyxSszVerification.CodecLaw
  via GenericContractProbe.restricted
""", "each exact child dictionary"),
}


def generic_contract_success():
    return PREFIX + POSITIVE


def generic_rejection_cases():
    return {name: (PREFIX + source, message) for name, (source, message) in NEGATIVE.items()}
