"""Pinned corpus schema declarations; all codec/root operations use remerkleable.

Shapes: consensus-specs tag v1.6.0-beta.0 (34ed95a58164d22b200df7ef4fb6dc1301599474),
tests/generators/runners/ssz_generic_cases/ssz_{progressive_,}container.py.
"""
from remerkleable.basic import uint8, uint16, uint32, uint64
from remerkleable.bitfields import Bitlist, Bitvector
from remerkleable.byte_arrays import ByteList
from remerkleable.complex import Container, List, Vector
from remerkleable.progressive import ProgressiveBitlist, ProgressiveContainer, ProgressiveList


def container(name, fields, active=None):
    base = Container if active is None else ProgressiveContainer(active_fields=active)
    return type(name, (base,), {"__annotations__": fields})


def schemas():
    single = container("SingleFieldTestStruct", {"A": uint8})
    small = container("SmallTestStruct", {"A": uint16, "B": uint16})
    fixed = container("FixedTestStruct", {"A": uint8, "B": uint64, "C": uint32})
    variable = container("VarTestStruct", {"A": uint16, "B": List[uint16, 1024], "C": uint8})
    complex_type = container("ComplexTestStruct", {"A": uint16, "B": List[uint16, 128], "C": uint8,
                             "D": ByteList[256], "E": variable, "F": Vector[fixed, 4], "G": Vector[variable, 2]})
    progressive = container("ProgressiveTestStruct", {"A": ProgressiveList[uint8], "B": ProgressiveList[uint64],
                            "C": ProgressiveList[small], "D": ProgressiveList[ProgressiveList[variable]]})
    bits = container("BitsStruct", {"A": Bitlist[5], "B": Bitvector[2], "C": Bitvector[1],
                                    "D": Bitlist[6], "E": Bitvector[8]})
    shapes = [Bitvector[256], Bitlist[256], ProgressiveBitlist, Bitvector[257], Bitlist[257], ProgressiveBitlist,
              Bitvector[1280], Bitlist[1280], ProgressiveBitlist, Bitvector[1281], Bitlist[1281], ProgressiveBitlist]
    progressive_bits = container("ProgressiveBitsStruct", dict(zip("ABCDEFGHIJKL", shapes)))
    psingle = container("ProgressiveSingleFieldContainerTestStruct", {"A": uint8}, [1])
    plist = container("ProgressiveSingleListContainerTestStruct", {"C": ProgressiveBitlist}, [0, 0, 0, 0, 1])
    pvar = container("ProgressiveVarTestStruct", {"A": uint8, "B": List[uint16, 123], "C": ProgressiveBitlist}, [1, 0, 1, 0, 1])
    positions = {0, 2, 4, 8, 12, 13, 20, 21}
    pcomplex = container("ProgressiveComplexTestStruct", {"A": uint8, "B": List[uint16, 123], "C": ProgressiveBitlist,
                         "D": ProgressiveList[uint64], "E": ProgressiveList[small],
                         "F": ProgressiveList[ProgressiveList[variable]], "G": List[psingle, 10],
                         "H": ProgressiveList[pvar]}, [int(i in positions) for i in range(22)])
    return {shape.__name__: shape for shape in [single, small, fixed, variable, complex_type, progressive, bits,
                                               progressive_bits, psingle, plist, pvar, pcomplex]}
