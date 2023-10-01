template <typename Event> class Select : public PushOperator<Event> {
  PushOperator<Event> *plan_;
  std::function<bool(Event &)> predicate_;

public:
  Select(PushOperator<Event> *plan, std::function<bool(Event &)> predicate)
      : plan_(plan), predicate_(predicate) {}

  void process(Event data) override {
    if (predicate_(data))
      plan_->process(std::move(data));
  }
};