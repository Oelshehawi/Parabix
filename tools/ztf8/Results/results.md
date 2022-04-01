Compression results on an extensively diverse set of Wikibooks files.

1. Basic compression and decompression.
* Min-max symbol length: 3-32 bytes
* Git tag: https://cs-git-research.cs.surrey.sfu.ca/cameron/parabix-devel/-/tags/CMP_DeCMP_v1
* Max number of Unicode word (ztf-symbol) in phrase: 2

| Filename | Size (MB) | Compressed size (MB) | Hashtable (MB) | Time (sec) | Decompression time (sec) |
|---------:|----------:|---------------------:|---------------:|----------: |-------------------------:|
|Arabic    | 18.7523   | 12.5694              | 2.2411         | 4.555      |0.502                     |
|German    | 195.48    | 153.91               | 3.5286         | 47.672     |5.474                     |
|Greek     | 18.7002   | 9.6006               | 2.6703         | 5.138      |0.681                     |
|Spanish   | 70.4887   | 53.196               | 2.1076         | 17.3       |2.024                     |
|Persian   | 19.2197   | 10.1089              | 1.8692         | 5.129      |0.681                     |
|Finnish   | 19.0433   | 13.361               | 2.1648         | 5.229      |0.689                     |
|French    | 87.567    | 64.1632              | 2.2984         | 21.211     |2.57                      |
|Indonesian| 14.4981   | 10.0327              | 1.0014         | 3.842      |0.546                     |
|Japanese  | 53.8666   | 47.1497              | 2.2697         | 12.791     |1.552                     |
|Korean    | 12.0246   | 9.737                | 1.1444         | 3.118      |0.457                     |
|Russian   | 56.4551   | 36.8118              | 3.624          | 14.462     |1.789                     |
|Thai      | 11.0458   | 9.2983               | 0.772476       | 2.825      |0.407                     |
|Turkish   | 11.7863   | 8.3733               | 1.5163         | 3.382      |0.468                     |
|Vietnamese| 11.2978   | 7.4577               | 0.84877        | 3.087      |0.44                      |
|Chinese   | 19.5651   | 14.5817              | 1.8406         | 5.064      |0.704                     |
|All-wiki  | 619.79    | 554.81               | 4.0436         | 148.873    |14.191                    |

1. Using scalable hashtable
* Min-max symbol length: 3-32 bytes
* Git commit SHA: 30e3dede9405064973af836fde2ce153df0e4b8b

| Filename | Size (MB) | Compressed size (MB) | Hashtable (MB) |
|---------:|----------:|---------------------:|---------------:|
|Arabic    | 18.7523   | 10.7836              | 3.7036         |
|German    | 195.48    | 145.47               | 8.5545         |
|Greek     | 18.7002   | 7.6456               | 4.3704         |
|Spanish   | 70.4887   | 50.9866              | 3.1941         |
|Persian   | 19.2197   | 9.1646               | 2.532          |
|Finnish   | 19.0433   | 12.1977              | 3.1733         |
|French    | 87.567    | 61.4654              | 3.5301         |
|Indonesian| 14.4981   | 9.5497               | 1.3796         |
|Japanese  | 53.8666   | 46.2149              | 3.1613         |
|Korean    | 12.0246   | 9.6029               | 1.297          |
|Russian   | 56.4551   | 29.6791              | 8.3315         |
|Thai      | 11.0458   | 9.2451               | 0.832972       |
|Turkish   | 11.7863   | 7.7808               | 2.0695         |
|Vietnamese| 11.2978   | 7.2636               | 1.0205         |
|Chinese   | 19.5651   | 14.138               | 2.3369         |
|All-wiki  | 619.79    | 539.53               | 12.505         |


1. Using weighted selection of hashtable entries
* Min-max symbol length: 3-32 bytes
* Segment size - 1048576 (1024^2) bytes
* Git commit SHA: 500bdbd03ab46b325a5dd70335d2fe35b618d5f7

| Filename | Size (MB) | Compressed file (MB) |  Decompression time (sec)  |
|---------:|----------:|---------------------:|---------------------------:|
|Arabic    | 18.7523   | 12.11                |  0.771                     |
|German    | 195.48    | 131.96               |  4.035                     |
|Greek     | 18.7002   | 9.81                 |  0.766                     |
|Spanish   | 70.4887   | 47.47                |  1.793                     |
|Persian   | 19.2197   | 10.11                |  0.784                     |
|Finnish   | 19.0433   | 12.96                |  0.751                     |
|French    | 87.567    | 56.89                |  2.067                     |
|Indonesian| 14.4981   | 9.54                 |  0.671                     |
|Japanese  | 53.8666   | 48.48                |  1.353                     |
|Korean    | 12.0246   | 10.45                |  0.584                     |
|Russian   | 56.4551   | 33.04                |  1.44                      |
|Thai      | 11.0458   | 9.69                 |  0.571                     |
|Turkish   | 11.7863   | 8.21                 |  0.606                     |
|Vietnamese| 11.2978   | 7.04                 |  0.564                     |
|Chinese   | 19.5651   | 14.93                |  0.726                     |
|All-wiki  | 619.79    | 444.46               |  11.206                    |

Decompression time (sec)
| real | user | sys |
|------|------|-----|
|0.329 |0.342 |0.10 |
|1.422 |2.138 |0.475|
|0.326 |0.303 |0.137|
|0.672 |0.877 |0.244|
|0.333 |0.301 |0.150|
|0.323 |0.292 |0.136|
|0.761 |1.058 |0.248|
|0.296 |0.202 |0.173|
|0.521 |0.642 |0.190|
|0.266 |0.194 |0.124|
|0.552 |0.716 |0.172|
|0.262 |0.167 |0.142|
|0.272 |0.208 |0.126|
|0.255 |0.199 |0.110|
|0.313 |0.264 |0.149|
|3.823 |6.459 |0.924|