
#include "Tables.h"

namespace tigl {
	MappingTable s_customTypes("../tables/CustomTypes.txt");
	MappingTable s_fundamentalTypes("../tables/FundamentalTypes.txt");
	MappingTable s_typeSubstitutions("../tables/TypeSubstitution.txt");
	MappingTable s_xsdTypes("../tables/XsdTypes.txt");

	Table s_parentPointers("../tables/ParentPointer.txt");
	Table s_reservedNames("../tables/ReservedNames.txt");
}
