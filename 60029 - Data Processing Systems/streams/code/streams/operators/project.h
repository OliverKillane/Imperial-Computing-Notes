template <typename InputEvent, typename OutputEvent = InputEvent>
class Project : public PushOperator<InputEvent> {
  PushOperator<OutputEvent> *plan_;
  std::function<OutputEvent(InputEvent)> function_;

public:
  Project(PushOperator<OutputEvent> *plan,
          std::function<OutputEvent(InputEvent)> function)
      : plan_(plan), function_(function) {}

  void process(InputEvent data) override {
    plan_->process(function_(std::move(data)));
  }
};