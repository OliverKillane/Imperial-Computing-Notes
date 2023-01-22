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

template <typename, typename> struct ConcatStruct;
template <typename... First, typename... Second>
struct ConcatStruct<std::tuple<First...>, std::tuple<Second...>> {
  using type = std::tuple<First..., Second...>;
};
template <typename L, typename R>
using Concat = typename ConcatStruct<L, R>::type;

template <typename LeftInputOperator, typename RightInputOperator>
struct CrossProduct
    : public Operator<Concat<typename LeftInputOperator::OutputType,
                             typename RightInputOperator::OutputType>> {
  LeftInputOperator leftInput;
  RightInputOperator rightInput;
  CrossProduct(LeftInputOperator leftInput, RightInputOperator rightInput)
      : leftInput(leftInput), rightInput(rightInput){};
};

template <typename LeftInputOperator, typename RightInputOperator>
struct Union : public Operator<typename LeftInputOperator::outputType> {

  LeftInputOperator leftInput;
  RightInputOperator rightInput;

  Union(LeftInputOperator leftInput, RightInputOperator rightInput)
      : leftInput(leftInput), rightInput(rightInput){};
};

template <typename LeftInputOperator, typename RightInputOperator>
struct Difference : public Operator<typename LeftInputOperator::outputType> {

  LeftInputOperator leftInput;
  RightInputOperator rightInput;

  Difference(LeftInputOperator leftInput, RightInputOperator rightInput)
      : leftInput(leftInput), rightInput(rightInput){};
};

template <typename LeftInputOperator, typename RightInputOperator>
struct Difference : public Operator<typename LeftInputOperator::outputType> {

  LeftInputOperator leftInput;
  RightInputOperator rightInput;

  Difference(LeftInputOperator leftInput, RightInputOperator rightInput)
      : leftInput(leftInput), rightInput(rightInput){};
};

// Aggregate functions to apply, 'agg' is for using groupAttributes
enum class AggregationFunction { min, max, sum, avg, count, agg };

template <typename InputOperator, typename... Output>
struct GroupedAggregation : public Operator<Output...> {
  InputOperator input;

  // the attributes to group by (column names)
  set<string> groupAttributes;

  // (column, aggregate function, new column name)
  set<tuple<string, AggregationFunction, string>> aggregations;

  GroupedAggregation(
      InputOperator input, set<string> groupAttributes,
      set<tuple<string, AggregationFunction, string>> aggregations)
      : input(input), groupAttributes(groupAttributes),
        aggregations(aggregations){};
};

// note that here we include N in the type (know at compile time), we could also
// take it as a parameter constructor (known at runtime)
template <typename InputOperator, size_t N>
struct TopN : public Operator<typename InputOperator::OutputType> {
  InputOperator input;
  string predicate;
  
  TopN(InputOperator input, string predicate)
      : input(input), predicate(predicate){};
};