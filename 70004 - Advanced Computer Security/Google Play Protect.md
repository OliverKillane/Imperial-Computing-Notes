## Definition
Previously called *Google Bouncer* which automatically scans new apps to look for malware.
- Checks not publicly disclosed
- Required to allow publishing on the Google Play Store.

| Static | Dynamic |
| ---- | ---- |
| Analyses paths from sources $\to$ sinks. (focused on sensitive sources, sinks being sensitive APIs) to determine what information the app collects. | Runs the app for 5 minutes in an emulator. Analyses to find hidden behaviour. |
Some manual analysis is included, likely flagged if the above techniques show suspicious behaviour. 
- Now claim machine learning is used.
- Noticeable improvement in the detections of malware.
