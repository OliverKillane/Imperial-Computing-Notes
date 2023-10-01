#include <iostream>
#include <vector>

// We create a basic NAry table type with type V (some std::variant<types>)
template <typename V> using Row = std::vector<V>;

template <typename V> using Table = std::vector<Row<V>>;

template <typename V>
size_t select_eq(Table<V> &outputBuffer, const Table<V> &inputBuffer,
                 V eq_value, size_t attribOffset) {

  for (const Row<V> &r : inputBuffer) {
    if (r[attribOffset] == eq_value) {
      outputBuffer.push_back(r);
    }
  }
  return outputBuffer.size();
}

void example_bulk() {
  // we can make a basic example with int only values as
  // CREATE TABLE Orders (orderId int, status int, urgency int);
  // C-style enums used for brevity
  enum Urgency { URGENT, NOT_URGENT, IGNORE };

  enum Status { COMPLETE, IN_PROCESS, PENDING };

  Table<int> Orders{
      {1, COMPLETE, IGNORE},
      {2, PENDING, IN_PROCESS},
      {3, PENDING, URGENT},
      {4, PENDING, URGENT},
  };

  Table<int> PendingOrders, UrgentAndPendingOrders;

  select_eq<int>(PendingOrders, Orders, PENDING, 1);
  select_eq<int>(UrgentAndPendingOrders, PendingOrders, URGENT, 2);

  for (auto &r : UrgentAndPendingOrders) {
    std::cout << "id: " << r[0] << std::endl;
  }
}

using Candidates = std::vector<uint32_t>;

template <typename V>
size_t add_candidates(const Table<V> &underlyingBuffer,
                      Candidates &outputRows) {
  for (uint32_t i = 0; i < underlyingBuffer.size(); i++) {
    outputRows.push_back(i);
  }
  return outputRows.size();
}

template <typename V>
size_t select_eq(const Table<V> &underlyingBuffer, Candidates &outputRows,
                 const Candidates &inputRows, V eq_value, size_t attribOffset) {
  for (const uint32_t index : inputRows) {
    if (underlyingBuffer[index][attribOffset] == eq_value) {
      outputRows.push_back(index);
    }
  }
  return outputRows.size();
}

void example_reference_bulk() {
  // we can make a basic example with int only values as
  // CREATE TABLE Orders (orderId int, status int, urgency int);
  // C-style enums used for brevity
  enum Urgency { URGENT, NOT_URGENT, IGNORE };

  enum Status { COMPLETE, IN_PROCESS, PENDING };

  Table<int> Orders{
      {1, COMPLETE, IGNORE},
      {2, PENDING, IN_PROCESS},
      {3, PENDING, URGENT},
      {4, PENDING, URGENT},
  };

  Candidates OrdersCandidates, PendingOrders, UrgentAndPendingOrders;
  add_candidates(Orders, OrdersCandidates);
  select_eq<int>(Orders, PendingOrders, OrdersCandidates, PENDING, 1);
  select_eq<int>(Orders, UrgentAndPendingOrders, PendingOrders, URGENT, 2);

  for (auto &r : UrgentAndPendingOrders) {
    std::cout << "id: " << Orders[r][0] << std::endl;
  }
}

int main() {
  example_bulk();
  example_reference_bulk();
}
