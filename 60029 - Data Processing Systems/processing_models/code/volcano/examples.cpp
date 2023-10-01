#include "operators.h"

/* Prints for debugging purposes */
template <class T>
std::ostream &operator<<(std::ostream &os, const std::vector<T> &vec) {
  os << "[";
  for (const auto &iter : vec) {
    os << " " << iter;
  }
  os << "]";
  return os;
}

/* Note: need to unwrap the T (otherwise will match empty parameter
 * pack/variadict template and fail of _Nth_type with 0 types).
 */
template <typename T, typename... Ts>
std::ostream &operator<<(std::ostream &os, const std::variant<T, Ts...> &var) {
  std::visit([&os](auto &&arg) { os << arg; }, var);
  return os;
}

template <typename T> void printConsume(Operator<T> &op) {
  op.open();
  for (auto val = op.next(); val.has_value(); val = op.next()) {
    std::cout << val.value() << std::endl;
  }
  op.close();
}

void example1() {
  std::cout << "SELECT *" << std::endl
            << "FROM table CROSS JOIN table;" << std::endl;

  std::shared_ptr<Table> data = std::make_shared<Table>(Table{{1, 'c', true},
                                                              {1, 'c', false},
                                                              {2, 'c', false},
                                                              {1, 'd', true},
                                                              {3, 'e', false}});

  auto scan1 = std::make_unique<Scan<Row>>(data);
  auto scan2 = std::make_unique<Scan<Row>>(data);
  auto cross = std::make_unique<CrossProduct<Row, Row>>(std::move(scan1),
                                                        std::move(scan2));

  Project<Row, std::tuple<Row, Row>> proj(
      std::move(cross), [](std::tuple<Row, Row> t) {
        auto vec2 = std::get<1>(t);
        auto vec1 = std::get<0>(t);
        vec1.insert(vec1.end(), vec2.begin(), vec2.end());
        return vec1;
      });

  printConsume(proj);
}

void example2() {
  std::cout << "SELECT table.1, table.2" << std::endl
            << "FROM table" << std::endl
            << "WHERE table.0 = 1;" << std::endl;
  std::shared_ptr<Table> data = std::make_shared<Table>(Table{{1, 'c', true},
                                                              {1, 'c', false},
                                                              {2, 'c', false},
                                                              {1, 'd', true},
                                                              {3, 'e', false}});

  auto scan = std::make_unique<Scan<Row>>(data);

  auto filter = std::make_unique<Select<Row>>(
      std::move(scan), [](Row r) { return std::get<int>(r[0]) == 1; });

  Project<Row, Row> proj(std::move(filter), [](Row r) {
    return Row{r[1], r[2]};
  });

  printConsume(proj);
}

size_t hashValue(Value v) { return std::hash<Value>{}(v); }
size_t nextSlotLinear(size_t prev) { return prev + 1; }

void example3() {
  std::cout << "SELECT table.1, MAX(table.0)" << std::endl
            << "FROM table" << std::endl
            << "GROUP BY table.1;" << std::endl;

  std::shared_ptr<Table> data = std::make_shared<Table>(Table{{1, 'c', true},
                                                              {1, 'd', true},
                                                              {1, 'c', false},
                                                              {2, 'c', false},
                                                              {5, 'c', false},
                                                              {3, 'e', false}});

  auto scan = std::make_unique<Scan<Row>>(data);

  // Group by for single column
  auto groupBySecondCol = [](Row r) { return r[1]; };
  auto aggregateSecondCol = [](std::optional<Row> r1, Row r2) {
    if (r1.has_value()) {
      return Row{std::max(std::get<int>(r1.value()[0]), std::get<int>(r2[0])),
                 r2[1]};
    } else {
      return Row{r2[0], r2[1]};
    }
  };

  GroupBy<Row, Row, Value, nextSlotLinear, hashValue> groupby(
      std::move(scan), groupBySecondCol, aggregateSecondCol);

  printConsume(groupby);
}

int main() {
  example1();
  example2();
  example3();
}