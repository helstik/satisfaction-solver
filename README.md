# Description
This program finds values to satisfy a compound proposition

# Usage
./main compound_proposition

# Example
Input proposition `(p & (q -> r) | m)`

Output
```m=true; p=false; q=false; r=false;
m=false; p=true; q=false; r=false;
m=true; p=true; q=false; r=false;
m=true; p=false; q=true; r=false;
m=true; p=true; q=true; r=false;
m=true; p=false; q=false; r=true;
m=false; p=true; q=false; r=true;
m=true; p=true; q=false; r=true;
m=true; p=false; q=true; r=true;
m=false; p=true; q=true; r=true;
m=true; p=true; q=true; r=true;
```
