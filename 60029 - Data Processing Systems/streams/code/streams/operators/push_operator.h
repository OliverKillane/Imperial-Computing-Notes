// templated by the Event data type (for easy testing), would be some
// vector<variant<int, float, string, ...>>
template <typename Event> class PushOperator {
public:
  virtual void process(Event data) = 0;
};