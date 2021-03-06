#pragma once

#include <boost/variant.hpp>
#include <boost/optional.hpp>

namespace tigl {
    template <typename... Ts>
    class Variant {
    public:
        Variant() {}

        template<typename T>
        Variant(const T& t) {
            m_data = t;
        }

        Variant(const Variant& other) {
            m_data = other.m_data;
        }

        Variant& operator=(const Variant& other) {
            m_data = other.m_data;
            return *this;
        }

        Variant(Variant&& other) {
            m_data = std::move(other.m_data);
        }

        Variant& operator=(Variant&& other) {
            m_data = std::move(other.m_data);
            return *this;
        }

        template<typename T>
        Variant& operator=(const T& t) {
            m_data = t;
            return *this;
        }

        template<typename Visitor>
        void visit(Visitor func) {
            if (m_data) {
                VisitorWrapper<Visitor> visitor(func);
                m_data->apply_visitor(visitor);
            }
        }

        template<typename Visitor>
        void visit(Visitor func) const {
            if (m_data) {
                VisitorWrapper<Visitor> visitor(func);
                m_data->apply_visitor(visitor);
            }
        }

        template<typename T>
        bool is() const {
            if (m_data)
                return m_data->type() == typeid(T);
            return false;
        }

        template<typename T>
        T& as() {
            return boost::get<T&>(*m_data);
        }

        template<typename T>
        const T& as() const {
            return boost::get<const T&>(*m_data);
        }

    private:
        // adapts a visitor for boost
        template <typename Func>
        struct VisitorWrapper : public boost::static_visitor<> {
            VisitorWrapper(Func func)
                : m_func(func) {}

            template<typename T>
            void operator()(T&& arg) {
                m_func(std::forward<T>(arg));
            }

        private:
            Func m_func;
        };

        boost::optional<boost::variant<Ts...>> m_data;
    };
}
