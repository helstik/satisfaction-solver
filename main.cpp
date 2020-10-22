#include <iostream>
#include <optional>
#include <variant>
#include <utility>
#include <vector>
#include <set>
#include <map>
#include <stack>
#include <sstream>
#include <cmath>

#ifdef TEST
#define CATCH_CONFIG_MAIN
#include "catch.hpp"
#endif


enum class Operator : uint8_t {
    negation,
    conjunction,
    disjunction,
    exclusive_or,
    implication,
    equivalence,
    left_bracket,
    right_bracket
};

auto precedence(const Operator op) -> size_t {
    switch (op) {
    case Operator::negation: return 3;
    case Operator::conjunction: return 2;
    case Operator::disjunction: return 1;
    case Operator::exclusive_or: return 1;
    case Operator::implication: return 0;
    case Operator::equivalence: return 0;
    case Operator::left_bracket: return -1;
    case Operator::right_bracket: return -1;
    }
}

struct Error {
    std::string description;
};

using Token = std::variant<Operator, std::string>;

template <class F>
void tokenize(std::string_view const string, F&& on_token_) {
    auto accumulator = std::string {};
    auto position = size_t {0};
    auto unexpected = [&](const char ch) {
        auto msg = std::string {"unexpected '"};
        msg += ch;
        msg += "' at ";
        msg += std::to_string(position);
        return msg;
    };
    auto on_token = [&](auto&& t) {
        const auto result = on_token_(std::move(t));
        accumulator.clear();
        return result;
    };
    auto on_separator = [&](const char sep) {
        if (accumulator.empty()) {
            return true;
        }

        if (accumulator == "(") {
            return on_token(Token {Operator::left_bracket});
        } else if (accumulator == ")") {
            return on_token(Token {Operator::right_bracket});
        } else if (accumulator.find_first_of("&|(+)-<>!") !=
                   std::string_view::npos) {
            return on_token(Error {unexpected(sep)});
            return false;
        }
        return on_token(Token {std::move(accumulator)});
    };
    auto has_operator_or_brace = [&]() {
        return accumulator.find_first_of("&|(+)-<>!") != std::string_view::npos;
    };
    auto on_operator_or_brace = [&]() {
        if (accumulator == "&") {
            return on_token(Token {Operator::conjunction});
        } else if (accumulator == "|") {
            return on_token(Token {Operator::disjunction});
        } else if (accumulator == "(+)") {
            return on_token(Token {Operator::exclusive_or});
        } else if (accumulator == "->") {
            return on_token(Token {Operator::implication});
        } else if (accumulator == "<->") {
            return on_token(Token {Operator::equivalence});
        } else if (accumulator == "!") {
            return on_token(Token {Operator::negation});
        } else if (accumulator == "(") {
            return on_token(Token {Operator::left_bracket});
        } else if (accumulator == ")") {
            return on_token(Token {Operator::right_bracket});
        } else {
            return false;
        }
        return true;
    };
#define ON_SEPARATOR         \
    if (!on_separator(ch)) { \
        return;              \
    }

#define ON_TOKEN(t)     \
    if (!on_token(t)) { \
        return;         \
    }

    for (const auto ch : string) {
        switch (ch) {
        case ' ': ON_SEPARATOR; break;
        case '&':
            ON_SEPARATOR;
            ON_TOKEN(Token {Operator::conjunction});
            break;
        case '|':
            ON_SEPARATOR;
            ON_TOKEN(Token {Operator::disjunction});
            break;
        case '(':
            ON_SEPARATOR;
            accumulator += ch;
            break;
        case '+':
            if (accumulator != "(") {
                ON_TOKEN(Error {unexpected(ch)});
                return;
            }
            accumulator += ch;
            break;
        case ')':
            if (accumulator == "(+") {
                ON_TOKEN(Token {Operator::exclusive_or});
            } else {
                ON_SEPARATOR;
                ON_TOKEN(Token {Operator::right_bracket});
            }
            break;
        case '-':
            if (!accumulator.empty() && accumulator != "<") {
                ON_TOKEN(Error {unexpected(ch)});
                return;
            }
            accumulator += ch;
            break;
        case '<':
            if (!accumulator.empty()) {
                ON_TOKEN(Error {unexpected(ch)});
                return;
            }
            accumulator += ch;
            break;
        case '>':
            if (accumulator == "-") {
                ON_TOKEN(Token {Operator::implication});
            } else if (accumulator == "<-") {
                ON_TOKEN(Token {Operator::equivalence});
            } else {
                ON_TOKEN(Error {unexpected(ch)});
            }
            break;
        case '!':
            ON_SEPARATOR;
            ON_TOKEN(Operator::negation);
            break;
        default:
            if (has_operator_or_brace()) {
                if (!on_operator_or_brace()) {
                    unexpected(ch);
                    return;
                }
            }
            accumulator += ch;
            break;
        }
        position += 1;
    }
    on_separator(' ');
#undef ON_TOKEN
#undef ON_SEPARATOR
}

auto get_token_vector(std::string_view const string)
    -> std::variant<Error, std::vector<Token>> {
    using Tokens = std::vector<Token>;

    auto result = std::variant<Error, Tokens> {std::in_place_type<Tokens>};
    auto on_token = [&](std::variant<Error, Token> either_token) {
        if (std::holds_alternative<Error>(either_token)) {
            result = std::move(std::get<Error>(either_token));
            return false;
        }
        auto& vector = std::get<Tokens>(result);
        vector.push_back(std::get<Token>(either_token));
        return true;
    };
    tokenize(string, on_token);
    return result;
}

using Tokens = std::vector<Token>;

auto operator<<(std::ostream& os, const Operator op) -> std::ostream& {
#define OPERATOR_STREAM_STRING(p) \
    case p: return os << "" #p;

    switch (op) {
        OPERATOR_STREAM_STRING(Operator::conjunction);
        OPERATOR_STREAM_STRING(Operator::disjunction);
        OPERATOR_STREAM_STRING(Operator::equivalence);
        OPERATOR_STREAM_STRING(Operator::exclusive_or);
        OPERATOR_STREAM_STRING(Operator::implication);
        OPERATOR_STREAM_STRING(Operator::negation);
        OPERATOR_STREAM_STRING(Operator::left_bracket);
        OPERATOR_STREAM_STRING(Operator::right_bracket);
    }
#undef OPERATOR_STREAM_STRING
}

template <class T>
auto is_error(const T& t) {
    return std::holds_alternative<Error>(t);
}

auto operator<<(std::ostream& os, const Token& token) -> std::ostream& {
    std::visit([&](const auto& v) { os << v; }, token);
    return os;
}

#ifdef TEST
TEST_CASE("Tokenize", "[parsing]") {
    SECTION("p & q") {
        const auto actual_or_error = get_token_vector("p & q");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {"p", Operator::conjunction, "q"};
        REQUIRE(actual == expected);
    }

    SECTION("p | q") {
        const auto actual_or_error = get_token_vector("p | q");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {"p", Operator::disjunction, "q"};
        REQUIRE(actual == expected);
    }

    SECTION("p (+) q") {
        const auto actual_or_error = get_token_vector("p (+) q");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {"p", Operator::exclusive_or, "q"};
        REQUIRE(actual == expected);
    }

    SECTION("p -> q") {
        const auto actual_or_error = get_token_vector("p -> q");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {"p", Operator::implication, "q"};
        REQUIRE(actual == expected);
    }

    SECTION("p <-> q") {
        const auto actual_or_error = get_token_vector("p <-> q");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {"p", Operator::equivalence, "q"};
        REQUIRE(actual == expected);
    }

    SECTION("!p") {
        const auto actual_or_error = get_token_vector("!p");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {Operator::negation, "p"};
        REQUIRE(actual == expected);
    }

    SECTION("!(p&q)") {
        const auto actual_or_error = get_token_vector("!(p&q)");
        REQUIRE(!is_error(actual_or_error));
        const auto& actual = std::get<Tokens>(actual_or_error);
        const auto expected = Tokens {Operator::negation,
                                      Operator::left_bracket,
                                      "p",
                                      Operator::conjunction,
                                      "q",
                                      Operator::right_bracket};
        REQUIRE(actual == expected);
    }
}
#endif

auto is_variable(const Token& token) -> bool {
    return std::holds_alternative<std::string>(token);
}

auto is_operator(const Token& token) -> bool {
    return std::holds_alternative<Operator>(token);
}

class ExpressionBuilder {
public:
    struct Result {
        std::set<std::string> variables;
        std::vector<Token> terms;
    };

    auto operator()(std::variant<Error, Token> maybe_token) -> bool {
        if (is_error(maybe_token)) {
            error_ = std::move(std::get<Error>(maybe_token));
            return false;
        }
        return on_token(std::get<Token>(maybe_token));
    }

    auto on_token(const Token& token) -> bool {
        return std::visit(
            [this](const auto& t) -> bool { return this->on_token_(t); },
            token);
    }

    auto build() -> std::variant<Error, Result> {
        if (error_) {
            return *error_;
        }
        pop_remaining();

        return Result {std::move(variables_), std::move(terms_)};
    }

private:
    auto on_token_(const std::string& variable_name) -> bool {
        if (0 == variables_.count(variable_name)) {
            variables_.emplace(variable_name);
        }
        terms_.push_back(variable_name);
        return true;
    }

    auto on_token_(const Operator op) -> bool {
        if (!operators_.empty()) {
            const auto top = operators_.top();
            if (Operator::right_bracket == op) {
                pop_until_left_bracket();
                return true;
            }
            if (Operator::left_bracket != top &&
                precedence(op) < precedence(top)) {
                pop_while_precedence_is_grater_than(precedence(op));
            }
        }
        operators_.push(op);
        return true;
    }

    void pop_until_left_bracket() {
        while (!operators_.empty() &&
               Operator::left_bracket != operators_.top()) {
            move_top_operator_to_terms();
        }
        if (!operators_.empty()) {
            operators_.pop();
        }
    }

    void pop_while_precedence_is_grater_than(const size_t threshold) {
        auto need_pop = [&]() -> bool {
            return !operators_.empty() &&
                   operators_.top() != Operator::left_bracket &&
                   precedence(operators_.top()) > threshold;
        };
        while (need_pop()) {
            move_top_operator_to_terms();
        }
    }

    void pop_remaining() {
        while (!operators_.empty()) {
            move_top_operator_to_terms();
        }
    }

    void move_top_operator_to_terms() {
        terms_.push_back(operators_.top());
        operators_.pop();
    }

    std::optional<Error> error_;
    std::vector<Token> terms_;
    std::stack<Operator> operators_;
    std::set<std::string> variables_;
};

#ifdef TEST
TEST_CASE("Parse", "[parsing]") {
    SECTION("p & q") {
        auto builder = ExpressionBuilder {};
        builder.on_token("p");
        builder.on_token(Operator::conjunction);
        builder.on_token("q");

        auto result_or_error = builder.build();
        REQUIRE(!is_error(result_or_error));
        const auto& build_result =
            std::get<ExpressionBuilder::Result>(result_or_error);
        const auto& variables = build_result.variables;
        REQUIRE(variables.size() == 2);
        REQUIRE(variables.find("p") != end(variables));
        REQUIRE(variables.find("q") != end(variables));
        const auto& terms = build_result.terms;
        REQUIRE(terms.size() == 3);
        REQUIRE(is_variable(terms[0]));
        REQUIRE(std::get<std::string>(terms[0]) == "p");
        REQUIRE(is_variable(terms[1]));
        REQUIRE(std::get<std::string>(terms[1]) == "q");
        REQUIRE(is_operator(terms[2]));
        REQUIRE(std::get<Operator>(terms[2]) == Operator::conjunction);
    }

    SECTION("p & q -> r") {
        auto builder = ExpressionBuilder {};
        builder.on_token("p");
        builder.on_token(Operator::conjunction);
        builder.on_token("q");
        builder.on_token(Operator::implication);
        builder.on_token("r");

        auto result_or_error = builder.build();
        REQUIRE(!is_error(result_or_error));
        const auto& build_result =
            std::get<ExpressionBuilder::Result>(result_or_error);
        const auto& variables = build_result.variables;
        REQUIRE(variables.size() == 3);
        REQUIRE(variables.find("p") != end(variables));
        REQUIRE(variables.find("q") != end(variables));
        REQUIRE(variables.find("r") != end(variables));
        const auto& terms = build_result.terms;
        REQUIRE(terms.size() == 5);
        REQUIRE(is_variable(terms[0]));
        REQUIRE(std::get<std::string>(terms[0]) == "p");
        REQUIRE(is_variable(terms[1]));
        REQUIRE(std::get<std::string>(terms[1]) == "q");
        REQUIRE(is_operator(terms[2]));
        REQUIRE(std::get<Operator>(terms[2]) == Operator::conjunction);
        REQUIRE(is_variable(terms[3]));
        REQUIRE(std::get<std::string>(terms[3]) == "r");
        REQUIRE(is_operator(terms[4]));
        REQUIRE(std::get<Operator>(terms[4]) == Operator::implication);
    }

    SECTION("p & (q -> r)") {
        auto builder = ExpressionBuilder {};
        builder.on_token("p");
        builder.on_token(Operator::conjunction);
        builder.on_token(Operator::left_bracket);
        builder.on_token("q");
        builder.on_token(Operator::implication);
        builder.on_token("r");
        builder.on_token(Operator::right_bracket);

        auto result_or_error = builder.build();
        REQUIRE(!is_error(result_or_error));
        const auto& build_result =
            std::get<ExpressionBuilder::Result>(result_or_error);
        const auto& variables = build_result.variables;
        REQUIRE(variables.size() == 3);
        REQUIRE(variables.find("p") != end(variables));
        REQUIRE(variables.find("q") != end(variables));
        REQUIRE(variables.find("r") != end(variables));
        const auto& terms = build_result.terms;
        REQUIRE(terms.size() == 5);
        REQUIRE(is_variable(terms[0]));
        REQUIRE(std::get<std::string>(terms[0]) == "p");
        REQUIRE(is_variable(terms[1]));
        REQUIRE(std::get<std::string>(terms[1]) == "q");
        REQUIRE(is_variable(terms[2]));
        REQUIRE(std::get<std::string>(terms[2]) == "r");
        REQUIRE(is_operator(terms[3]));
        REQUIRE(std::get<Operator>(terms[3]) == Operator::implication);
        REQUIRE(is_operator(terms[4]));
        REQUIRE(std::get<Operator>(terms[4]) == Operator::conjunction);
    }

    SECTION("(p | q) & (q | r)") {
        auto builder = ExpressionBuilder {};
        builder.on_token(Operator::left_bracket);
        builder.on_token("p");
        builder.on_token(Operator::disjunction);
        builder.on_token("q");
        builder.on_token(Operator::right_bracket);
        builder.on_token(Operator::conjunction);
        builder.on_token(Operator::left_bracket);
        builder.on_token("q");
        builder.on_token(Operator::disjunction);
        builder.on_token("r");
        builder.on_token(Operator::right_bracket);

        const auto result_or_error = builder.build();
        REQUIRE(!is_error(result_or_error));
        const auto& [variables, terms] =
            std::get<ExpressionBuilder::Result>(result_or_error);
        REQUIRE(variables.size() == 3);
        REQUIRE(variables.find("p") != end(variables));
        REQUIRE(variables.find("q") != end(variables));
        REQUIRE(variables.find("r") != end(variables));

        REQUIRE(terms.size() == 7);
        REQUIRE(is_variable(terms[0]));
        REQUIRE(std::get<std::string>(terms[0]) == "p");
        REQUIRE(is_variable(terms[1]));
        REQUIRE(std::get<std::string>(terms[1]) == "q");
        REQUIRE(is_operator(terms[2]));
        REQUIRE(std::get<Operator>(terms[2]) == Operator::disjunction);
        REQUIRE(is_variable(terms[3]));
        REQUIRE(std::get<std::string>(terms[3]) == "q");
        REQUIRE(is_variable(terms[4]));
        REQUIRE(std::get<std::string>(terms[4]) == "r");
        REQUIRE(is_operator(terms[5]));
        REQUIRE(std::get<Operator>(terms[5]) == Operator::disjunction);
        REQUIRE(is_operator(terms[6]));
        REQUIRE(std::get<Operator>(terms[6]) == Operator::conjunction);
    }

    SECTION("(p & (q -> r) | m)") {
        auto builder = ExpressionBuilder {};
        builder.on_token(Operator::left_bracket);
        builder.on_token("p");
        builder.on_token(Operator::conjunction);
        builder.on_token(Operator::left_bracket);
        builder.on_token("q");
        builder.on_token(Operator::implication);
        builder.on_token("r");
        builder.on_token(Operator::right_bracket);
        builder.on_token(Operator::disjunction);
        builder.on_token("m");
        builder.on_token(Operator::right_bracket);

        const auto result_or_error = builder.build();
        REQUIRE(!is_error(result_or_error));
        const auto& [variables, terms] =
            std::get<ExpressionBuilder::Result>(result_or_error);
        REQUIRE(variables.size() == 4);
        REQUIRE(variables.find("p") != end(variables));
        REQUIRE(variables.find("q") != end(variables));
        REQUIRE(variables.find("r") != end(variables));
        REQUIRE(variables.find("m") != end(variables));

        REQUIRE(terms.size() == 7);
        REQUIRE(is_variable(terms[0]));
        REQUIRE(std::get<std::string>(terms[0]) == "p");
        REQUIRE(is_variable(terms[1]));
        REQUIRE(std::get<std::string>(terms[1]) == "q");
        REQUIRE(is_variable(terms[2]));
        REQUIRE(std::get<std::string>(terms[2]) == "r");
        REQUIRE(is_operator(terms[3]));
        REQUIRE(std::get<Operator>(terms[3]) == Operator::implication);
        REQUIRE(is_operator(terms[4]));
        REQUIRE(std::get<Operator>(terms[4]) == Operator::conjunction);
        REQUIRE(is_variable(terms[5]));
        REQUIRE(std::get<std::string>(terms[5]) == "m");
        REQUIRE(is_operator(terms[6]));
        REQUIRE(std::get<Operator>(terms[6]) == Operator::disjunction);
    }
}
#endif

template <class F>
auto evaluate(const std::vector<Token>& expression, F&& get_variable_value)
    -> std::variant<Error, bool> {
    auto stack = std::stack<bool> {};

    auto implication = [](const bool lhs, const bool rhs) -> bool {
        return !lhs || rhs;
    };
    auto exclusive_or = [](const bool lhs, const bool rhs) -> bool {
        return (lhs || rhs) && (!rhs || !lhs);
    };
    auto get_function =
        [&](const Operator op) -> std::function<bool(bool, bool)> {
        switch (op) {
        case Operator::conjunction: return std::logical_and {};
        case Operator::disjunction: return std::logical_or {};
        case Operator::exclusive_or: return exclusive_or;
        case Operator::implication: return implication;
        case Operator::equivalence: return std::equal_to<bool> {};
        default: assert(!"unreacheble");
        }
    };

    auto pop_binary_operands = [&stack]() -> std::pair<bool, bool> {
        const auto rhs = stack.top();
        stack.pop();
        const auto lhs = stack.top();
        stack.pop();
        return {lhs, rhs};
    };

    for (auto it = begin(expression); it != end(expression); it = next(it)) {
        const auto& term = *it;
        if (is_variable(term)) {
            auto value = get_variable_value(std::get<std::string>(term));
            if (is_error(value)) {
                return std::move(std::get<Error>(value));
            }
            stack.push(std::get<bool>(value));
            continue;
        }

        const auto op = std::get<Operator>(term);
        if (stack.empty()) {
            auto msg = std::ostringstream {};
            msg << "got " << op << ", but stack is empty";
            return Error {msg.str()};
        }

        if (Operator::negation == op) {
            const auto top = stack.top();
            stack.pop();
            stack.push(!top);
            continue;
        }

        if (stack.size() < 2) {
            auto msg = std::ostringstream {};
            msg << "not enough operands for " << op;
            return Error {msg.str()};
        }

        const auto [lhs, rhs] = pop_binary_operands();
        stack.push(get_function(op)(lhs, rhs));
    }

    assert(stack.size() == 1);
    return stack.top();
}

#ifdef TEST
TEST_CASE("Evaluate", "[evaluate]") {
    auto values = std::map<std::string, bool> {};
    const auto get_value =
        [&](const std::string& v) -> std::variant<Error, bool> {
        if (auto res = values.find(v); res != end(values)) {
            return res->second;
        }
        return Error {"variable " + v + " is not found"};
    };

    SECTION("p -> q") {
        values.clear();
        const auto expression =
            std::vector<Token> {"p", "q", Operator::implication};
        SECTION("T -> T") {
            values["p"] = true;
            values["q"] = true;
            const auto result = evaluate(expression, get_value);
            REQUIRE(!is_error(result));
            REQUIRE(std::get<bool>(result) == true);
        }

        SECTION("T -> F") {
            values["p"] = true;
            values["q"] = false;
            const auto result = evaluate(expression, get_value);
            REQUIRE(std::get<bool>(result) == false);
        }

        SECTION("F -> T") {
            values["p"] = false;
            values["q"] = true;
            const auto result = evaluate(expression, get_value);
            REQUIRE(std::get<bool>(result) == true);
        }

        SECTION("F -> F") {
            values["p"] = false;
            values["q"] = false;
            const auto result = evaluate(expression, get_value);
            REQUIRE(std::get<bool>(result) == true);
        }
    }

    SECTION("(p | q) & (q | r)") {
        values.clear();
        const auto expression = std::vector<Token> {"p",
                                                    "q",
                                                    Operator::disjunction,
                                                    "q",
                                                    "r",
                                                    Operator::disjunction,
                                                    Operator::conjunction};

        SECTION("(T | T) & (T | T)") {
            values["p"] = true;
            values["q"] = true;
            values["r"] = true;
            const auto result = evaluate(expression, get_value);
            REQUIRE(!is_error(result));
            REQUIRE(std::get<bool>(result) == true);
        }

        SECTION("(T | T) & (T | F)") {
            values["p"] = true;
            values["q"] = true;
            values["r"] = false;
            const auto result = evaluate(expression, get_value);
            REQUIRE(!is_error(result));
            REQUIRE(std::get<bool>(result) == true);
        }

        SECTION("(T | F) & (F | T)") {
            values["p"] = true;
            values["q"] = false;
            values["r"] = true;
            const auto result = evaluate(expression, get_value);
            REQUIRE(!is_error(result));
            REQUIRE(std::get<bool>(result) == true);
        }

        SECTION("(T | F) & (F | F)") {
            values["p"] = true;
            values["q"] = false;
            values["r"] = false;
            const auto result = evaluate(expression, get_value);
            REQUIRE(!is_error(result));
            REQUIRE(std::get<bool>(result) == false);
        }
    }
}
#endif

class CombinationGenerator {
public:
    template <class T>
    CombinationGenerator(const T& variables)
        : max_(std::pow(2, variables.size())) {
        for (const auto& name : variables) {
            variables_.emplace(name, false);
        }
    }

    /*
     * @return indicates whether a generator reached the end
     */
    auto advance() -> bool {
        current_ += 1;
        if (max_ == current_) {
            return false;
        }
        for (auto it = begin(variables_); it != end(variables_); it = next(it)) {
            auto& [name, value] = *it;
            (void)name;
            if (!value) {
                value = true;
                break;
            }

            const auto next_it = next(it);
            if (end(variables_) == next_it) {
                continue;
            }
            
            auto& next_value = next_it->second;
            if (value && !next_value) {
                for_each(begin(variables_), next_it,
                         [](auto& v) { return v.second = false; });
                next_value = true;
                break;
            }
        }

        return true;
    }

    auto variables() const -> const std::map<std::string, bool>& {
        return variables_;
    }

private:
    std::map<std::string, bool> variables_;
    size_t current_ = 0;
    size_t max_;
};

#ifdef TEST
TEST_CASE("CombinationGenerator", "[generate]") {
    auto generator = CombinationGenerator(std::array {"1", "2", "3"});
    const auto& variables = generator.variables();
    const auto to_vector = [&]() {
        auto res = std::vector<bool> {};
        res.reserve(variables.size());
        transform(begin(variables), end(variables), std::back_inserter(res),
                  [](const auto& v) { return v.second; });
        return res;
    };
    REQUIRE(to_vector() == std::vector{false, false, false});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{true, false, false});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{false, true, false});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{true, true, false});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{false, false, true});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{true, false, true});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{false, true, true});
    REQUIRE(generator.advance());
    REQUIRE(to_vector() == std::vector{true, true, true});
    REQUIRE(!generator.advance());
}
#endif

#ifndef CATCH_CONFIG_MAIN
auto main(const int argc, const char** argv) -> int {
    if (2 != argc) {
        std::cout << "Usage " << argv[0] << " compound_proposition" << std::endl;
        return 0;
    }

    auto builder = ExpressionBuilder {};
    tokenize(argv[1], builder);
    const auto build_result = builder.build();
    if (is_error(build_result)) {
        std::cerr << "Parsing error " << std::get<Error>(build_result).description << std::endl;
        return 1;
    }

    const auto& expression_data =
        std::get<ExpressionBuilder::Result>(build_result);
    auto combination_generator =
        CombinationGenerator {expression_data.variables};
    const auto& variables = combination_generator.variables();
    const auto get_value =
        [&](const std::string& name) -> std::variant<Error, bool> {
        if (const auto it = variables.find(name); it != end(variables)) {
            return it->second;
        }
        return Error {"variable " + name + " is not found"};
    };

    const auto print_variables = [&]() {
        std::cout << std::boolalpha;
        for(const auto& [name, value] : variables) {
            std::cout << name << '=' << value << "; ";
        }
        std::cout << std::noboolalpha;
        std::cout << std::endl;
    };
    do {
        const auto result_or_error = evaluate(expression_data.terms, get_value);
        if (is_error(result_or_error)) {
            std::cerr << "Evaluation error " << std::get<Error>(result_or_error).description << std::endl;
            return 1;
        }
        const auto result = std::get<bool>(result_or_error);
        if (!result) {
            continue;
        }
        print_variables();
    } while (combination_generator.advance());
    return 0;
}
#endif
