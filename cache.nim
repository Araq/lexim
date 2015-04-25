

import db_sqlite

let db = open(connection="lexim.db", user="", password="", database="cache")

db.exec(sql"""
  create table if not exists Table1(
    id integer primary key,
    key varchar(256) not null,
    value varchar(256) not null,
    created timestamp not null default (DATETIME('now'))
  );

  create unique index if not exists KeyIx on Table1(key);
  """)

proc get*(key: string): string =
  db.getValue(sql"select value from Table1 where key = ?", key)

proc put*(key, value: string) =
  db.exec sql"insert into Table1(key, value) values (?, ?)", key, value
  close db

