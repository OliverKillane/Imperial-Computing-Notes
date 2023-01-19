// Compile with C++ 20 (g++ -std=c++2a relation.cc)
#include <array>
#include <functional>
#include <set>
#include <string>
#include <tuple>
#include <variant>

using namespace std;

template <typename... types> struct Relation {
  using OutputType = tuple<types...>;

  set<tuple<types...>> data;
  array<string, sizeof...(types)> schema;

  Relation(array<string, sizeof...(types)> schema, set<tuple<types...>> data)
      : schema(schema), data(data) {}
};

auto rel_example() {
  return Relation<string, int, int>(
      {"Name", "Age", "Review"},
      {{"Jim", 33, 3}, {"Jay", 23, 5}, {"Mick", 34, 4}});
}

template <typename... types> struct Operator : public Relation<types...> {};

template <typename InputOperator, typename... outputTypes>
struct Project : public Operator<outputTypes...> {
  InputOperator input;
  variant<function<tuple<outputTypes...>(typename InputOperator::OutputType)>,
          set<pair<string, string>>>
      projections;

  Project(InputOperator input,
          function<tuple<outputTypes...>(typename InputOperator::OutputType)>
              projections)
      : input(input), projections(projections) {}

  Project(InputOperator input, set<pair<string, string>> projections)
      : input(input), projections(projections) {}
};

// enum classes are preferred over enums as:
// 1. The enumerations are within the scope of the enum
// 2. There is no implicit conversion (e.g to ints)
enum class Comparator { less, lessEqual, equal, greaterEqual, greater };

struct Column {
  string name;
  Column(string name) : name(name) {}
};

// type alias for comparable values
using Value = variant<string, int, float>;

struct Condition {
  Comparator compare;

  Column leftHandSide;
  variant<Column, Value> rightHandSide;

  Condition(Column leftHandSide, Comparator compare,
            variant<Column, Value> rightHandSide)
      : leftHandSide(leftHandSide), compare(compare),
        rightHandSide(rightHandSide) {}
};

template <typename LeftInputOperator, typename RightInputOperator>
struct CrossProduct
    : public Operator<Concat<typename LeftInputOperator::OutputType,
                             typename RightInputOperator::OutputType>> {
  LeftInputOperator leftInput;
  RightInputOperator rightInput;
  CrossProduct(LeftInputOperator leftInput, RightInputOperator rightInput)
      : leftInput(leftInput), rightInput(rightInput){};
};
