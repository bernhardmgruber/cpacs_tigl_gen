#include "TypeSystem.h"

#include <boost/algorithm/string.hpp>
#include <boost/range/adaptors.hpp>

#include <iostream>
#include <cctype>
#include <fstream>

#include "NotImplementedException.h"
#include "Tables.h"

namespace tigl {
    namespace {
        auto buildSchemaDependencies(const xsd::SchemaTypes& types, const MappingTable& xsdTypes) -> std::unordered_map<std::string, std::vector<std::string>> {
            std::cout << "Building dependencies" << std::endl;

            std::unordered_map<std::string, std::vector<std::string>> allDeps;

            for (auto& p : types.types) {
                auto& v = p.second;
                if (v.is<xsd::SimpleType>()) {
                    auto& st = v.as<xsd::SimpleType>();
                    allDeps[st.name];
                    continue;
                }

                auto& c = v.as<xsd::ComplexType>();
                auto& deps = allDeps[c.name];

                // base
                if (!c.base.empty())
                    deps.push_back(c.base);

                // attributes
                for (const auto& a : c.attributes)
                    deps.push_back(a.type);

                // elements
                struct ContentVisitor : public boost::static_visitor<> {
                    ContentVisitor(std::vector<std::string>& deps)
                        : deps(deps) {}

                    void operator()(const xsd::Element& e) const {
                        deps.push_back(e.type);
                    }

                    void operator()(const xsd::Choice& c) const {
                        for (const auto& v : c.elements)
                            v.visit(*this);
                    }

                    void operator()(const xsd::Sequence& s) const {
                        for (const auto& v : s.elements)
                            v.visit(*this);
                    }

                    void operator()(const xsd::All& a) const {
                        for (const auto& e : a.elements)
                            operator()(e);
                    }

                    void operator()(const xsd::Any& a) const {
                        throw NotImplementedException("Building dependencies for any is not implemented");
                    }

                    void operator()(const xsd::Group& g) const {
                        throw NotImplementedException("Building dependencies for group is not implemented");
                    }

                    void operator()(const xsd::SimpleContent& g) const {
                        deps.push_back(g.type);
                    }

                private:
                    std::vector<std::string>& deps;
                };

                c.content.visit(ContentVisitor(deps));

                std::sort(std::begin(deps), std::end(deps));
                deps.erase(std::unique(std::begin(deps), std::end(deps)), std::end(deps));
                deps.erase(std::remove_if(std::begin(deps), std::end(deps), [&](const std::string& d){
                    return xsdTypes.contains(d);
                }), std::end(deps));
            }

            return allDeps;
        }

        auto checkAndPrintNode(const std::string& name, const Table& pruneList, unsigned int level) {
            if (pruneList.contains(name)) {
                std::cout << std::string(level, '\t') << "pruning " << name << std::endl;
                return true;
            }
            else {
                std::cout << std::string(level, '\t') << "including " << name << std::endl;
                return false;
            }
        }

        void includeNode(const std::unordered_map<std::string, std::vector<std::string>>& deps, std::unordered_set<std::string>& includedTypes, const std::string& name, const Table& pruneList, unsigned int level) {
            // if this class is already included, return
            if (includedTypes.count(name))
                return;

            // if this class is on the prune list, just omit it and all its sub element types
            if (checkAndPrintNode(name, pruneList, level))
                return;

            // class is not pruned, include it
            includedTypes.insert(name);

            // try to include all dependencies
            for (auto& d : deps.at(name))
                includeNode(deps, includedTypes, d, pruneList, level + 1);
        }

        auto runPruneList(const std::vector<std::string>& roots, std::unordered_map<std::string, std::vector<std::string>> deps, const Table& pruneList) -> std::unordered_set<std::string> {
            std::unordered_set<std::string> includedTypes;

            // recurse on all root nodes
            for (const auto& root : roots) {
                std::cout << "Running prune list starting at " << root << std::endl;
                includeNode(deps, includedTypes, root, pruneList, 0);
            }

            std::cout << "The following types have been pruned:" << std::endl;
            std::vector<std::string> prunedTypeNames;
            for (const auto& d : deps)
                if (!includedTypes.count(d.first))
                    prunedTypeNames.push_back(d.first);
            std::sort(std::begin(prunedTypeNames), std::end(prunedTypeNames));
            for (const auto& name : prunedTypeNames)
                std::cout << "\t" << name << std::endl;

            return includedTypes;
        }

        auto simplifyAndCollapseEnums(xsd::SchemaTypes types) -> xsd::SchemaTypes {
            // move all enums out of the types
            std::vector<xsd::SimpleType> sts;
            for (auto it = begin(types.types); it != end(types.types); ) {
                if (it->second.is<xsd::SimpleType>()) {
                    sts.push_back(std::move(it->second.as<xsd::SimpleType>()));
                    it = types.types.erase(it);
                } else
                    ++it;
            }

            // sort by enum name for determinism
            std::sort(begin(sts), end(sts), [](const xsd::SimpleType& a, const xsd::SimpleType& b) {
                return a.name < b.name;
            });

            std::unordered_map<std::string, std::string> replacedEnums;

            auto stripEnum = [](std::string name) {
                // handle inline enum types
                // generated names are of the form: <containing type name>_<element name>[_SimpleContent][_<counter>][Type]

                // strip Type suffix from <containing type name> if exists
                name = xsd::stripTypeSuffix(name);

                // remove optional digits and underscore at the end
                while (!name.empty() && std::isdigit(name.back()))
                    name.pop_back();
                if (name.back() == '_')
                    name.pop_back();

                // remove _SimpleContent
                name = xsd::stripSimpleContentSuffix(name);

                // if type contains an underscore, remove preceding part
                const auto& pos = name.find_last_of('_');
                if (pos != std::string::npos)
                    name.erase(0, pos + 1);

                // capitalize first letter
                name[0] = std::toupper(name[0]);

                // strip Type suffix from <containing type name> if exists
                name = xsd::stripTypeSuffix(name);

                //// prefix CPACS if not exists
                //if (name.compare(0, 5, "CPACS") != 0)
                //    name = "CPACS" + name;

                return name;
            };

            auto nameAvailable = [&](const std::string& name) {
                return std::find_if(begin(sts), end(sts), [&](const xsd::SimpleType& st) {
                    return st.name == name;
                }) == end(sts) && std::find_if(begin(replacedEnums), end(replacedEnums), [&](const auto& p) {
                    return p.second == name;
                }) == end(replacedEnums);
            };

            //std::cout << "Simplifying enums" << std::endl;
            //for (auto& st : sts) {
            //    auto newName = stripEnum(st.name);
            //    if (!nameAvailable(newName) || st.name == newName) {
            //        std::cout << "\t" << st.name << " failed" << std::endl;
            //        continue;
            //    }

            //    std::cout << "\t" << st.name << " to " << newName << std::endl;
            //    replacedEnums[st.name] = newName;
            //    st.name = newName;
            //}

            std::cout << "Collapsing enums" << std::endl;

            for (std::size_t i = 0; i < sts.size(); i++) {
                auto& e1 = sts[i];

                for (std::size_t j = i + 1; j < sts.size(); j++) {
                    auto& e2 = sts[j];

                    // check for equal enum values
                    if (e1.restrictionValues == e2.restrictionValues) {
                        // strip name decorators
                        const auto& e1StrippedName = stripEnum(e1.name);
                        const auto& e2StrippedName = stripEnum(e2.name);
                        if (e1StrippedName == e2StrippedName) {
                            // choose new name
                            const auto newName = [&] {
                                // if the stripped name is not already taken, use it. Otherwise, take the shorter of the two enum names
                                if (nameAvailable(e1StrippedName))
                                    return e1StrippedName;
                                else
                                    return std::min(e1.name, e2.name);
                            }();

                            // register replacements
                            if (e1.name != newName) replacedEnums[e1.name] = newName;
                            if (e2.name != newName) replacedEnums[e2.name] = newName;

                            std::cout << "\t" << e1.name << " and " << e2.name << " to " << newName << std::endl;

                            // rename e1 and remove e2
                            e1.name = newName;
                            sts.erase(begin(sts) + j);
                            j--;
                        }
                    }
                }
            }

            // replace enum names
            struct TypeRenameVisitor : public boost::static_visitor<> {
                TypeRenameVisitor(const std::unordered_map<std::string, std::string>& replacedEnums)
                    : replacedEnums(replacedEnums) {}

                void tryReplaceType(std::string& name) const {
                    const auto& it = replacedEnums.find(name);
                    if (it != std::end(replacedEnums))
                        name = it->second;
                }

                void operator()(xsd::Element& e) const {
                    tryReplaceType(e.type);
                }

                void operator()(xsd::Choice& c) const {
                    for (auto& v : c.elements)
                        v.visit(*this);
                }

                void operator()(xsd::Sequence& s) const {
                    for (auto& v : s.elements)
                        v.visit(*this);
                }

                void operator()(xsd::All& a) const {
                    for (auto& e : a.elements)
                        operator()(e);
                }

                void operator()(xsd::Any& a) const {
                    throw NotImplementedException("any is not implemented");
                }

                void operator()(xsd::Group& g) const {
                    throw NotImplementedException("group is not implemented");
                }

                void operator()(xsd::SimpleContent& g) const {
                    tryReplaceType(g.type);
                }

                void operator()(xsd::ComplexType& g) const {
                    for (auto& a : g.attributes)
                        tryReplaceType(a.type);
                    g.content.visit(*this);
                }

                void operator()(xsd::SimpleType& st) const {
                    tryReplaceType(st.name);
                }

            private:
                const std::unordered_map<std::string, std::string>& replacedEnums;
            };

            for (auto& t : types.types)
                t.second.visit(TypeRenameVisitor{ replacedEnums });

            // put enums back in
            for (auto& st : sts)
                types.types[st.name] = std::move(st);

            return types;
        }

        auto makeClassName(std::string name) -> std::string {
            if (!name.empty()) {
                // capitalize first letter
                name[0] = std::toupper(name[0]);

                // strip Type suffix if exists
                name = xsd::stripTypeSuffix(name);

                // prefix CPACS
                name = "CPACS" + name;
            }

            return name;
        }

        auto resolveType(const xsd::SchemaTypes& types, const std::string& name, const Tables& tables) -> std::string {
            // search simple and complex types
            const auto cit = types.types.find(name);
            if (cit != std::end(types.types)) {
                // apply type substitution
                if (const auto p = tables.m_typeSubstitutions.find(name))
                    return *p;
                else
                    return makeClassName(name);
            }

            // search predefined xml schema types and replace them
            if (const auto p = tables.m_xsdTypes.find(name))
                return *p;

            throw std::runtime_error("Unknown type: " + name);
        }

        auto buildFieldListAndChoiceExpression(const xsd::SchemaTypes& types, const xsd::ComplexType& type, std::function<bool(const std::string&)> isPruned, const Tables& tables) -> std::tuple<std::vector<Field>, ChoiceElements> {
            std::vector<Field> members;
            ChoiceElements choiceItems;

            // attributes
            for (const auto& a : type.attributes) {
                if (isPruned(a.type))
                    continue;

                Field m;
                m.originXPath = a.xpath;
                m.cpacsName = a.name;
                m.typeName = resolveType(types, a.type, tables);
                m.xmlType = XMLConstruct::Attribute;
                m.minOccurs = a.optional ? 0 : 1;
                m.maxOccurs = 1;
                m.defaultValue = a.defaultValue;
                members.push_back(m);
            }

            // elements
            struct ContentVisitor : public boost::static_visitor<> {
                ContentVisitor(const xsd::SchemaTypes& types, std::vector<Field>& members, ChoiceElements& choiceItems, std::size_t attributeCount, std::function<bool(const std::string&)> isPruned, const Tables& tables, std::vector<std::size_t> choiceIndices = {})
                    : types(types), members(members), choiceItems(choiceItems), attributeCount(attributeCount), isPruned(isPruned), tables(tables), choiceIndices(choiceIndices) {}

                void emitField(Field f) const {
                    if (!choiceIndices.empty()) {
                        // make optional
                        const auto minBefore = f.minOccurs;
                        f.minOccurs = 0;

                        // give custom name
                        f.namePostfix = "_choice" + boost::join(choiceIndices | boost::adaptors::transformed([](std::size_t i) { return std::to_string(i); }), "_");

                        choiceItems.push_back(ChoiceElement{ members.size(), minBefore == 0 });
                    }
                    members.push_back(std::move(f));
                }

                void operator()(const xsd::Element& e) const {
                    if (isPruned(e.type))
                        return;

                    if (e.minOccurs == 0 && e.maxOccurs == 0) {
                        std::cerr << "Warning: Element " + e.name + " with type " + e.type + " was omitted as minOccurs and maxOccurs are both zero" << std::endl;
                        return; // skip this type
                    }

                    Field m;
                    m.originXPath = e.xpath;
                    m.cpacsName = e.name;
                    m.typeName = resolveType(types, e.type, tables);
                    m.xmlType = XMLConstruct::Element;
                    m.minOccurs = e.minOccurs;
                    m.maxOccurs = e.maxOccurs;
                    m.defaultValue = e.defaultValue;
                    emitField(std::move(m));
                }

                void operator()(const xsd::Choice& c) const {
                    const auto countBefore = members.size();

                    Choice choice;
                    for (const auto& v : c.elements | boost::adaptors::indexed(1)) {
                        // collect members of one choice
                        auto indices = choiceIndices;
                        indices.push_back(v.index());
                        ChoiceElements subChoiceItems;
                        v.value().visit(ContentVisitor(types, members, subChoiceItems, attributeCount, isPruned, tables, indices));
                        choice.options.push_back(std::move(subChoiceItems));
                    }
                    choiceItems.push_back(std::move(choice));

                    // consistency check, two types with the same name but different types or cardinality are problematic
                    for (std::size_t i = countBefore; i < members.size(); i++) {
                        const auto& f1 = members[i];
                        for (std::size_t j = i + 1; j < members.size(); j++) {
                            const auto& f2 = members[j];
                            if (f1.cpacsName == f2.cpacsName && (f1.cardinality() != f2.cardinality() || f1.typeName != f2.typeName)) {
                                std::cerr << "Elements with same name but different cardinality or type inside choice" << std::endl;
                                for (const auto& f : { f1, f2 })
                                    std::cerr << f.cpacsName << " " << toString(f.cardinality()) << " " << f.typeName << std::endl;
                            }
                        }
                    }
                }

                void operator()(const xsd::Sequence& s) const {
                    const auto countBefore = members.size();
                    for (const auto& v : s.elements)
                        v.visit(*this);
                    // if the sequence was optional, make all the elements optional
                    if (s.minOccurs == 0)
                        for (auto i = countBefore; i < members.size(); i++)
                            members[i].minOccurs = 0;
                }

                void operator()(const xsd::All& a) const {
                    const auto countBefore = members.size();
                    for (const auto& e : a.elements)
                        operator()(e);

                    // if the all was optional, make all the elements optional
                    if (a.minOccurs == 0)
                        for (auto i = countBefore; i < members.size(); i++)
                            members[i].minOccurs = 0;
                }

                void operator()(const xsd::Any& a) const {
                    throw NotImplementedException("Generating fields for any is not implemented");
                }

                void operator()(const xsd::Group& g) const {
                    throw NotImplementedException("Generating fields for group is not implemented");
                }

                void operator()(const xsd::SimpleContent& g) const {
                    if (isPruned(g.type))
                        return;

                    Field m;
                    m.originXPath = g.xpath;
                    m.cpacsName = "";
                    m.namePostfix = "simpleContent";
                    m.minOccurs = 1;
                    m.maxOccurs = 1;
                    m.typeName = resolveType(types, g.type, tables);
                    m.xmlType = XMLConstruct::SimpleContent;
                    emitField(std::move(m));
                }

            private:
                const xsd::SchemaTypes& types;
                std::vector<Field>& members;
                ChoiceElements& choiceItems;
                const std::size_t attributeCount;
                std::function<bool(const std::string&)> isPruned;
                const Tables& tables;
                const std::vector<std::size_t> choiceIndices; // not empty when inside a choice
            };

            type.content.visit(ContentVisitor(types, members, choiceItems, members.size(), isPruned, tables));

            return std::make_tuple(members, choiceItems);
        }
    }

    class TypeSystemBuilder {
    public:
        TypeSystemBuilder(xsd::SchemaTypes types, std::function<bool(const std::string&)> isPruned, const Tables& tables)
            : m_types(std::move(types)), isPruned(isPruned), tables(tables) {}

        void build() {
            for (const auto& p : m_types.types) {
                const auto& type = p.second;

                struct TypeVisitor {
                    TypeVisitor(const xsd::SchemaTypes& types, TypeSystemBuilder& typeSystem, const Tables& tables)
                        : types(types), typeSystem(typeSystem), tables(tables) {}

                    void operator()(const xsd::ComplexType& type) {
                        if (typeSystem.isPruned(type.name) || tables.m_typeSubstitutions.contains(type.name))
                            return;

                        Class c;
                        c.originXPath = type.xpath;
                        c.name = makeClassName(type.name);
                        std::tie(c.fields, c.choices) = buildFieldListAndChoiceExpression(types, type, typeSystem.isPruned, tables);

                        if (typeSystem.isPruned(c.base))
                            c.base.clear();

                        if (!type.base.empty()) {
                            c.base = resolveType(types, type.base, tables);

                            // make base a field if fundamental type
                            if (tables.m_fundamentalTypes.contains(c.base)) {
                                std::cout << "\tWarning: Type " << type.name << " has base class " << c.base << " which is a fundamental type. Generated field 'base' instead" << std::endl;

                                Field f;
                                f.cpacsName = "";
                                f.namePostfix = "base";
                                f.minOccurs = 1;
                                f.maxOccurs = 1;
                                f.typeName = c.base;
                                f.xmlType = XMLConstruct::FundamentalTypeBase;

                                c.fields.insert(std::begin(c.fields), f);
                                c.base.clear();
                            }
                        }

                        typeSystem.m_classes[c.name] = c;
                    }

                    void operator()(const xsd::SimpleType& type) {
                        if (typeSystem.isPruned(type.name) || tables.m_typeSubstitutions.contains(type.name))
                            return;

                        if (type.restrictionValues.size() > 0) {
                            // create enum
                            Enum e;
                            e.originXPath = type.xpath;
                            e.name = makeClassName(type.name);
                            for (const auto& v : type.restrictionValues)
                                e.values.push_back(EnumValue(v));
                            typeSystem.m_enums[e.name] = e;
                        } else
                            throw NotImplementedException("Simple types which are not enums are not implemented: " + type.name);
                    }

                private:
                    const xsd::SchemaTypes& types;
                    TypeSystemBuilder& typeSystem;
                    const Tables& tables;
                };

                type.visit(TypeVisitor(m_types, *this, tables));
            }
        }

        // TODO: replace by lambda when C++14 is available
        struct SortAndUnique {
            template <typename T>
            void operator()(std::vector<T*>& con) {
                std::sort(std::begin(con), std::end(con), [](const T* a, const T* b) {
                    return a->name < b->name;
                });
                con.erase(std::unique(std::begin(con), std::end(con), [](const T* a, const T* b) {
                    return a->name == b->name;
                }), std::end(con));
            }
        };

        void buildDependencies() {
            std::cout << "Building dependencies" << std::endl;

            for (auto& p : m_classes) {
                auto& c = p.second;
                // base
                if (!c.base.empty()) {
                    const auto it = m_classes.find(c.base);
                    if (it != std::end(m_classes)) {
                        c.deps.bases.push_back(&it->second);
                        it->second.deps.deriveds.push_back(&c);
                    } else
                        // this exception should be prevented by earlier code
                        throw std::runtime_error("Class " + c.name + " has non-class base: " + c.base);
                }

                // fields
                for (auto& f : c.fields) {
                    const auto eit = m_enums.find(f.typeName);
                    if (eit != std::end(m_enums)) {
                        c.deps.enumChildren.push_back(&eit->second);
                        eit->second.deps.parents.push_back(&c);
                    } else {
                        const auto cit = m_classes.find(f.typeName);
                        if (cit != std::end(m_classes)) {
                            c.deps.children.push_back(&cit->second);
                            cit->second.deps.parents.push_back(&c);
                        }
                    }
                }
            }

            SortAndUnique sortAndUnique;

            // sort and unique
            for (auto& p : m_classes) {
                auto& c = p.second;
                sortAndUnique(c.deps.bases);
                sortAndUnique(c.deps.children);
                sortAndUnique(c.deps.deriveds);
                sortAndUnique(c.deps.enumChildren);
                sortAndUnique(c.deps.parents);
            }

            for (auto& p : m_enums) {
                auto& e = p.second;
                sortAndUnique(e.deps.parents);
            }
        }

        void prefixClashedEnumValues() {
            std::unordered_map<std::string, std::vector<Enum*>> valueToEnum;

            for (auto& p : m_enums) {
                auto& e = p.second;
                for (auto& v : e.values) {
                    auto& otherEnums = valueToEnum[v.name()];
                    if (otherEnums.size() == 1) {
                        // we are adding the same enum value for the second time
                        // prefix other enum's value
                        auto& otherEnum = *otherEnums[0];
                        const auto it = std::find_if(std::begin(otherEnum.values), std::end(otherEnum.values), [&](const EnumValue& ov) {
                            return ov.name() == v.name();
                        });
                        if (it == std::end(otherEnum.values))
                            throw std::logic_error("Enum value resolves to an enum which does not have the value");
                        it->customName = otherEnum.name + "_" + it->cpacsName;
                    }
                    if (otherEnums.size() > 1) {
                        // we are adding an already added value, prefix myself
                        v.customName = e.name + "_" + v.cpacsName;
                    }

                    otherEnums.push_back(&e);
                }
            }

            std::cout << "Prefixed the following enum values:" << std::endl;
            for (auto& p : valueToEnum) {
                const auto& otherEnums = p.second;
                if (otherEnums.size() > 1) {
                    std::cout << '\t' << p.first << std::endl;
                    for (const auto& e : otherEnums)
                        std::cout << "\t\t" << e->name << std::endl;
                }
            }
        }

        const Tables& tables;
        xsd::SchemaTypes m_types;
        std::function<bool(const std::string&)> isPruned;
        std::unordered_map<std::string, Class> m_classes;
        std::map<std::string, Enum> m_enums;
    };

    auto buildTypeSystem(xsd::SchemaTypes types, const Tables& tables) -> TypeSystem {
        types = simplifyAndCollapseEnums(std::move(types));

        const auto deps = buildSchemaDependencies(types, tables.m_xsdTypes);
        auto includedTypes = runPruneList(types.roots, deps, tables.m_pruneList);

        auto isPruned = [&](const std::string& name) {
            return !tables.m_xsdTypes.contains(name) && !includedTypes.count(name);
        };

        TypeSystemBuilder builder(std::move(types), isPruned, tables);
        builder.build();
        builder.buildDependencies();
        builder.prefixClashedEnumValues();
        return {
            std::move(builder.m_classes),
            std::move(builder.m_enums)
        };
    }

    void writeGraphVisFile(const TypeSystem& ts, const std::string& typeSystemGraphVisFile) {
        std::cout << "Writing type system graph vis file to " << typeSystemGraphVisFile << std::endl;
        std::ofstream f{typeSystemGraphVisFile};
        if (!f)
            throw std::runtime_error("Failed to open file " + typeSystemGraphVisFile + " for writing");
        f << "digraph typesystem {\n";
        for (const auto& p : ts.classes) {
            const auto& c = p.second;
            for (const auto& b : c.deps.bases)
                f << "\t" << c.name << " -> " << b->name << ";\n";
            for (const auto& ch : c.deps.children)
                f << "\t" << c.name << " -> " << ch->name << ";\n";
            for (const auto& e : c.deps.enumChildren)
                f << "\t" << c.name << " -> " << e->name << ";\n";
        }
        // enums have no further dependencies
        f << "}\n";
    }
}
