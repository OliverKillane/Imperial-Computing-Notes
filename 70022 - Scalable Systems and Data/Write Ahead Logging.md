A technique used for atomicity & durability in ACID databases.
- Every operation to modify the database is logged on disk before the contents of the associated page are modified.
- Hence cannot make a change without at least it's log (from which it can be reconstructed) being persisted.
- Can checkpoint the log periodically (make all logged changes to the database persisted, then can clear out the logfile)