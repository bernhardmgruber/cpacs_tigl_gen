#pragma once

#include "Table.h"

class XsdTypesTable : public Table {
public:
	XsdTypesTable()
		: Table({
			{ "xsd:byte",         "int8_t" },
			{ "xsd:unsignedByte", "uint8_t" },
			{ "xsd:short",        "int16_t" },
			{ "xsd:unsignedShort","uint16_t" },
			{ "xsd:int",          "int32_t" },
			{ "xsd:unsignedInt",  "uint32_t" },
			{ "xsd:long"    ,     "int64_t" },
			{ "xsd:unsignedLong", "uint64_t" },
			{ "xsd:integer",      "int" },
			{ "xsd:boolean",      "bool" },
			{ "xsd:float",        "float" },
			{ "xsd:double",       "double" },
			{ " xsd:decimal",      "double" }, // TODO: implement custom type?
			{ "xsd:dateTime",     "time_t" },
			{ "xsd:string",       "std::string" },
		}) {}
};