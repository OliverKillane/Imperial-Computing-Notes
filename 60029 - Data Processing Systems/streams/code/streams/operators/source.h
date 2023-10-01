template <typename Event> class Source {
public:
  virtual void run() = 0;
};

template <typename Event> class UserInput : public Source<Event> {
  PushOperator<Event> *plan_;
  std::istream &src_;

public:
  UserInput(PushOperator<Event> *plan, std::istream &src)
      : plan_(plan), src_{src} {}

  void run() override {
    for (Event r;; src_ >> r)
      plan_->process(std::move(r));
  }
};
