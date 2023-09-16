# include <iostream>
# include <stdio.h>
# include <vector>
# include <string.h>
# include <string>
# include <cmath>
# include <cstdlib>
# include <iomanip>
# include <sstream>

# define LEFT 1
# define RIGHT 2
# define INT 3
# define FLOAT 4
# define STRING 5
# define DOT 6
# define NIL 7
# define T 8
# define QUOTE 9
# define SYMBOL 10
# define STRINGs 11

# define cmdNum 41

using namespace std ;

int gTestNum = 0 ;

class PL {
public:

  struct DATA {
    bool inter ;
    bool mean ;
    bool finish ;
    int token ;          // S-exp類型(貨物類型)
    char element[256] ;  // 拆分後的token(貨物內容)
    int line ;           // 行標籤
    int column ;         // 列標籤
    int addr ;
    DATA * next ;
    DATA * down ;
  };

  DATA * m_current ;  // 備份未展開的樹
  DATA * m_head ;     // 紀錄結構的頭
  DATA * m_function ; // 紀錄binding
  DATA * m_pos ;      // 紀錄m_function 進入let前位置
  DATA * m_walk ;
  DATA * m_temp ;
  DATA * m_error ;
  DATA * m_cond ;     // cond
  DATA * m_para ;     // 紀錄定義的function
  DATA * m_tmpara ;

  int m_line ;    // 行
  int m_column ;  // 列
  int m_clk ;
  int m_left ;
  int m_coda ;
  bool m_power;   // 工廠鉉作能源電閘

  void Semantics( int err, int & end ) {  // ------------------------- 語意判斷
    int left = 0, index = 0, pair = 0 ;
    bool back = false ;
    m_head = new DATA ;
    NewNode( m_head ) ; // head指向結構的頭
    m_temp = m_head ;
    BuildDS( m_temp, left, back ) ;

    m_walk = m_head ;
    m_current = new DATA ;
    NewNode( m_current ) ;
    m_current = CopyPointer( m_current, m_head ) ;

    bool printDirectly = false, eqv = false, preDef = false ;
    bool if_cond = false, eLse = false, finish = false ;

    if ( m_walk->next == NULL && m_walk->down == NULL ) { // atom && symbol
      bool isBound = false ;
      if ( m_walk->token == SYMBOL ) { // symbol判斷bounding
        m_walk = Preprocesor( m_walk, preDef, isBound ) ;
        if ( !isBound ) {
          err = 5 ;
          m_error = m_head ;
        } // if

        if ( !m_walk->inter && m_walk->token == LEFT )
          m_head = Evaluate( m_walk, m_walk, printDirectly, preDef, if_cond, finish, 0, err, false ) ;

      } // if
    } // if
    else {
      m_head = Evaluate( m_walk, m_walk, printDirectly, preDef, if_cond, finish, 0, err, false ) ;
      if ( m_head->token == LEFT &&
           strcmp( m_head->down->element, "#<procedure exit>" ) == 0 &&
           m_head->down->next->token == RIGHT ) end = 1 ;
    } // else

    if ( end == 1 ) ;
    else Print( err ) ;

  } // Semantics()

  void Semantics_sub( DATA * m_walk, DATA * local, bool if_cond, int & err, bool isfun ) {  // ------------------------- 語意判斷

    bool printDirectly = false, eqv = false, preDef = false ;
    bool eLse = false, finish = false ;

    if ( m_walk->next == NULL && m_walk->down == NULL ) { // atom && symbol

      bool isBound = false ;
      if ( m_walk->token == SYMBOL ) { // symbol判斷bounding
        m_walk = Preprocesor( m_walk, preDef, isBound ) ;
        if ( !isBound && ! m_walk->mean ) {
          err = 5 ;
          m_error = m_walk ;
        } // if

        if ( !m_walk->inter && m_walk->token == LEFT )
          m_cond = Evaluate( m_walk, m_walk, printDirectly, preDef, if_cond, finish, 0, err, isfun ) ;

      } // if
    } // if
    else m_cond = Evaluate( m_walk, m_walk, printDirectly, preDef, if_cond, finish, 0, err, isfun ) ;

  } // Semantics_sub()

  DATA * Evaluate( DATA * m_walk, DATA * shead, bool & printDirectly, bool Def, bool if_cond, bool & finish,
                   int level, int & err, bool isfun ) {

    bool isBound = false, nowElse = false ;
    DATA * temp = new DATA ;
    char * p ;
    DATA * local = new DATA ;

    NewNode( temp ) ;
    CopyPointer( temp, m_walk ) ;

    if ( shead == m_walk ) { // 處存一份不展開的
      NewNode( local ) ;
      local = CopyPointer( local, m_walk ) ;
      if ( level != 0 ) {
        DATA * qua = new DATA ;
        NewNode( qua ) ;
        qua->token = LEFT ;
        strcpy( qua->element, "(" ) ;
        qua->down = local ;
        local = qua ;
      } // if
    } // if

    m_walk = Preprocesor( m_walk, false, isBound ) ;

    if ( shead == m_walk && !CheckErr( m_walk, local, isBound, Def, if_cond, level, err, false ) ) {
      if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
        if ( m_error == NULL ) m_error = local ;
      } // if

      return m_walk ;  // 第一個指令需要檢查後面文法
    } // if
    else if ( Def && shead->next == m_walk && strcmp( shead->element, "#<procedure define>" ) == 0 ) {
      if ( m_current->down->next->token == LEFT ) return m_walk ;
    } // else if
    else if ( shead->next == m_walk && strcmp( shead->element, "#<procedure lambda>" ) == 0 ) {
      bool have = false ;
      for ( DATA * h = m_para ; h != NULL ; h = h->down ) {
        if ( h->addr == shead->addr ) have = true ;
      } // for

      if ( ! have ) return m_walk ;
    } // else if
    else if ( shead != m_walk && !isBound && ! m_walk->mean ) {
      err = 5 ;
      m_walk->next = NULL ;
      m_error = m_walk ;
      return m_walk ;
    } // else if

    if ( shead == m_walk &&  ( strcmp( shead->element, "#<procedure cond>" ) == 0 ||
                               strcmp( shead->element, "#<procedure if>" ) == 0 ||
                               strcmp( shead->element, "#<procedure let>" ) == 0 ) ) {
      if ( strcmp( shead->element, "#<procedure cond>" ) == 0 )
        m_walk->next = Peek_cond( m_walk->next, err, local ) ;
      else if ( strcmp( shead->element, "#<procedure if>" ) == 0 )
        m_walk->next = Peek_if( m_walk->next, err, local ) ;
      else if ( strcmp( shead->element, "#<procedure let>" ) == 0 )
        m_walk->next = Peek_let( m_walk->next, err, local ) ;
      /*
      if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
        if ( local->down != NULL )
          cout << "**********" << local->down->element << endl ;
        m_error = local ;
        
        return m_walk ;
      } // if
      else */
      if ( err != -1 ) return m_walk ;

      else {
        printDirectly = true ;
        m_walk = m_walk->next ;
        m_walk->next = NULL ;
        return m_walk ;
      } // else
    } // if

    if ( shead == m_walk && strcmp( m_walk->element, "#<procedure quote>" ) == 0 ) ;
    else {

      if ( m_walk->down != NULL && m_walk->down->line != -1 && ! m_walk->finish )  // 向下遞迴!!!!!!!!!!!!!
        m_walk->down = Evaluate( m_walk->down, m_walk->down,
                                 printDirectly, Def, if_cond, finish, level+1, err, isfun ) ;

      if ( err == 18 && shead != m_walk && m_coda == 1 && !isfun ) {   // no return value (且為參數情況)
        //cout << shead->element << "        " << m_walk->element << endl ;
        
        if ( strcmp( shead->element, "#<procedure begin>" ) == 0 &&
             ( m_walk->next != NULL && m_walk->next->token != RIGHT ) ) err = -1 ;
        else err = 20 ;
        
        m_coda = 0 ;
        if ( err != -1 ) return m_walk ;
      } // if
      
      else if ( err == 18 && shead == m_walk && level == 1 && strcmp( m_walk->element, "(" ) == 0 && 
                !isfun && m_coda == 0 ) {
        
        err = 20 ;
        m_coda = 0 ;
        if ( err != -1 ) return m_walk ;
      } // else if
      
      else if ( err == 18 && shead != m_walk ) {
        //cout << "--------- " << m_walk->element ;
        //if ( m_walk->next != NULL ) cout << "    " << m_walk->next->element << endl ;
        //else cout << endl ;
        //if ( !isfun ) cout << "!isfun   " << m_coda << endl ;
        //else cout << "not fun" << endl ;
        if ( strcmp( shead->element, "#<procedure begin>" ) == 0 &&
             ( m_walk->next != NULL && m_walk->next->token != RIGHT ) ) err = -1 ;
             
        else if ( strcmp( shead->element, "#<procedure cond>" ) == 0 ||
                  strcmp( shead->element, "#<procedure if>" ) == 0 ) err = 21 ;
        else if ( strcmp( shead->element, "#<procedure and>" ) == 0 ||
                  strcmp( shead->element, "#<procedure or>" ) == 0 ) err = 22 ;
        /*
        if ( err == 21 || err == 22 ) {
          DATA * t = shead ;
          for ( DATA * h = local->down ; h != NULL && m_error == NULL ; h = h->next ) {
            if ( t == m_walk ) {
              m_error = h ;
              m_error->next = NULL ;
            } // if
            t = t->next ;
          } // for
        } // if
        */
        cout << "++++++++++++++++++++" << shead->element << endl ;
        m_error = local ;
        if ( !isfun && level != 0 ) {
          m_coda = 0 ;
        } // if
        
        if ( err != -1 ) return m_walk ;
      } // else if
      
      else if ( err != -1 ) return m_walk ;

      if ( finish ) {
        finish = false ;
        m_walk->finish = true ;
      } // if
      else if ( printDirectly ) {
        printDirectly = false ;
        if ( m_walk->down != NULL && m_walk->down->down != NULL && 
             strcmp( m_walk->down->down->element, ")" ) == 0 )  {
          strcpy( m_walk->down->element, "nil" ) ;
          m_walk->down->token = NIL ;
          m_walk->down->down = NULL ;
        } // if
        
        if ( level == 0 ) {
          return m_walk->down ;
        } // if
        
        if ( level == 1 ) {  //  *******************************
          if ( err == 18 && shead == m_walk && strcmp( m_walk->element, "(" ) == 0 && 
               !isfun && m_coda == 0 ) {
        
            err = 20 ;
            m_coda = 0 ;
            if ( err != -1 ) return m_walk ;
          } // if
        } // if
        
        if ( shead == m_walk ) {
          DATA * tmp = m_walk->next ;
          m_walk = m_walk->down ;
          shead = m_walk ;
          m_walk->next = tmp ;
        } // if
        else {
          DATA * tmp = shead ;
          while ( tmp->next != m_walk ) tmp = tmp->next ;
          m_walk->down->next = tmp->next->next ;
          tmp->next = m_walk->down ;
          m_walk = m_walk->down ;
        } // else

        isBound = false ;

        if ( shead == m_walk && level != 0 &&
             !CheckErr( m_walk, local, isBound, Def, if_cond, level, err, true ) ) {
          if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
            m_error = local ;
          } // if

          return m_walk ;
        } // if

      } // if
      else {
        if ( shead == m_walk && level != 0 &&
             !CheckErr( m_walk, local, isBound, Def, if_cond, level, err, true ) ) {
          if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
            m_error = local ;
          } // if

          return m_walk ;
        } // if
        
        if ( m_walk->down != NULL && strcmp( m_walk->down->element, ")" ) == 0 )  {
          strcpy( m_walk->element, "nil" ) ;
          m_walk->token = NIL ;
          m_walk->down = NULL ;
        } // if
      } // else

      if ( shead == m_walk && m_walk->next == NULL ) return m_walk ;
      if ( !Def && shead != m_walk && m_walk->token != RIGHT && !CheckErr2( m_walk, shead, local, err ) ) {
        if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
          m_error = local ;

        } // if

        return m_walk ;
      } // if

      if ( m_walk->next != NULL )  // 向右遞迴!!!!!!!!!!!!!!!!!!
        m_walk->next = Evaluate( m_walk->next, shead, printDirectly, Def, if_cond, finish, level+1, err, isfun ) ;
      if ( shead != m_walk || err != -1 ) return m_walk ;
    } // else


    if ( strcmp( m_walk->element, "#<procedure list>" ) == 0 ) {
      finish = true ;
      return m_walk->next ;
    } // if
    else if ( strcmp( m_walk->element, "#<procedure exit>" ) == 0 ) {
      return m_walk ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure quote>" ) == 0 ) {
      printDirectly = true ;
      m_walk->next->next = NULL ;
      Finish( m_walk->next ) ;
      return m_walk->next ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure cons>" ) == 0 ) {
      finish = true ;
      m_walk = m_walk->next ;  // 第一個參數
      if ( strcmp( m_walk->next->element, "(" ) == 0 ) { // 第二個參數是expr
        DATA * temp = m_walk->next->down ;
        m_walk->next = temp ;
        return m_walk ;
      } // if
      else if ( strcmp( m_walk->next->element, "nil" ) == 0 ||
                strcmp( m_walk->next->element, "#f" ) == 0 ) { // 第二個參數是nil
        DATA * temp = new DATA ;
        NewNode( temp ) ;
        strcpy( temp->element, ")" ) ;
        temp->token = RIGHT ;
        m_walk->next = temp ;
        return m_walk ;
      } // if
      else {       // 第二個參數是數字
        DATA * temp = new DATA ;
        NewNode( temp ) ;
        strcpy( temp->element, "." ) ;
        temp->token = DOT ;
        temp->next = m_walk->next ;
        m_walk->next = temp ;

        m_walk->line = -1 ; // 利用line來標示此tokrn為pair
        return m_walk ;
      } // else
    } // if
    else if ( strcmp( m_walk->element, "#<procedure car>" ) == 0 ) {
      printDirectly = true ;
      m_walk->next->down->next = NULL ;

      return m_walk->next->down ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure cdr>" ) == 0 ) {
      printDirectly = true ;
      if ( m_walk->next->down->next != NULL ) {
        if ( strcmp( m_walk->next->down->next->element, "." ) != 0 ) {
          m_walk->next->next = NULL ;
          m_walk->next->down = m_walk->next->down->next ;
          return m_walk->next ;
        } // if
        else {

          m_walk->next->down->next->next->next = NULL ;      // . 後面的元素 的後面會接 ')' 去掉')'
          return m_walk->next->down->next->next ;
        } // else
      } // if
      else return NULL ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ) {

      printDirectly = true ;
      DATA * temp = new DATA ;
      NewNode( temp ) ;
      if ( m_current->down->next->token == LEFT )
        strcpy( temp->element, m_current->down->next->down->element ) ;
      else strcpy( temp->element, m_current->down->next->element ) ;
      strcat( temp->element, " defined" ) ;
      temp->token = SYMBOL ;

      Define( m_walk ) ;

      return temp ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure clean-environment>" ) == 0 ) {
      m_function = NULL ;
      m_para = NULL ;
      m_tmpara = NULL ;
      printDirectly = true ;
      DATA * temp = new DATA ;
      NewNode( temp ) ;
      strcpy( temp->element, "environment cleaned" ) ;
      temp->token = SYMBOL ;
      Load() ;
      return temp ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure +>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure ->" ) == 0 ||
              strcmp( m_walk->element, "#<procedure *>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure />" ) == 0 ) {

      printDirectly = true ;
      return Arithmetic( m_walk, m_walk->element, err ) ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure not>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure and>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure or>" ) == 0 ) {

      printDirectly = true ;
      return LogicOperation( m_walk ) ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure eqv?>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure equal?>" ) == 0 ) {
      printDirectly = true ;
      return Equal( m_walk ) ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure >=>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure <=>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure >>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure <>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure =>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure string-append>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure string>?>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure string<?>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure string=?>" ) == 0 ) {

      printDirectly = true ;
      return Compare( m_walk, m_walk->element ) ;
    } // else if
    else if ( m_walk->element[ strlen( m_walk->element )-2 ] == '?' ) {   // 判斷型別 ex: string?
      printDirectly = true ;
      return JudgmentType( m_walk ) ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure begin>" ) == 0 ) {
      printDirectly = true ;
      return Begin( m_walk ) ;
    } // else if
    else if ( strcmp( m_walk->element, "#<procedure lambda>" ) == 0 ) { // 定義

      DATA * pos = m_tmpara ;
      for ( DATA * h = m_para ; h != NULL ; h = h->down ) {
        if ( h->addr == shead->addr ) {
          printDirectly = true ;
          return Lamb_do( m_walk, err ) ;
        } // if
      } // for

      Give( m_walk ) ; // 給每個lambda 一個號碼牌

      DATA * temp = m_walk->next->next ; // EXP頭

      if ( m_walk->next->token == NIL ) {
        DATA * l = new DATA ;
        NewNode( l ) ;
        DATA * r = new DATA ;
        NewNode( r ) ;
        strcpy( l->element, "(" ) ;
        strcpy( r->element, ")" ) ;
        l->token = LEFT ;
        r->token = RIGHT ;
        l->down = r ;
        m_walk->next = l ;
        m_walk->next->next = temp ;
      } // if

      for ( DATA * m = m_walk ; m != NULL ; m = m->next ) // 把最後)削掉
        if ( m->next->token == RIGHT ) m->next = NULL ;


      m_walk = new DATA ;
      NewNode( m_walk ) ;
      m_walk = CopyPointer( m_walk, shead ) ;
      DATA * t = m_para ;
      m_para = m_walk ;
      m_para->down = t ;
      t = m_para ;

      printDirectly = true ;
      shead->next = NULL ;
      return shead ;
    } // else if
    else {
      DATA * tmpara = NULL ;   // 紀錄binding的參數
      DATA * pos = m_tmpara ;
      DATA * m = NULL ;

      printDirectly = true ;
      DATA * walk = NULL ;
      DATA * fun = m_para ;
      bool find = false ;
      DATA * tmp = shead->next ;

      for ( ; fun != NULL && !find ; fun = fun->down ) { // 找function
        if ( strcmp( fun->element, shead->element ) == 0 ) {
          find = true ;
          m = fun ;
          for ( fun = fun->next->down ; fun->token != RIGHT ; fun = fun->next ) { // 接參數
            DATA * t = new DATA ;
            NewNode( t ) ;
            Copy( t, fun, fun->element ) ;
            t->next = new DATA ;
            NewNode( t->next ) ;
            t->next = CopyPointer( t->next, tmp ) ;
            t->next->next = NULL ;
            if ( walk == NULL ) {
              walk = t ;
              tmpara = walk ;
            } // if
            else {
              walk->down = t;
              walk = walk->down ;
            } // else

            tmp = tmp->next ;
          } // for

          fun = m->next->next ;
          m_cond = new DATA ;
          NewNode( m_cond ) ;
          CopyPointer( m_cond, fun ) ;
        } // if
      } // for

      tmp = m_cond ;
      if ( m_tmpara == NULL ) m_tmpara = tmpara ;
      else {
        DATA * t = tmpara ;

        while ( t != NULL && t->down != NULL ) t = t->down ;
        if ( t != NULL ) t->down = m_tmpara ;
        m_tmpara = tmpara ;
      } // else

      DATA * nextOne = NULL ;
      DATA * copy = NULL ;
      bool stop = false ;
      while ( m_cond != NULL && !stop ) {   // 要evaluate每個exp 並return最後一個值
        nextOne = m_cond->next ;
        m_cond->next = NULL ;
        DATA * tmp2 = m_cond ;
        
        copy = new DATA ;
        NewNode( copy ) ;
        copy = CopyPointer( copy, m_cond ) ;
        
        Semantics_sub( tmp2, copy, false, err, true ) ;

        if ( ( err == 18 || err == 20 || err == 21 || err == 22 ) && nextOne != NULL )
          err = -1 ;    // return no value 但不是在最後一個
        
        if ( err != -1 ) stop = true ;

        if ( nextOne == NULL ) copy = m_cond ;
        m_cond->next = nextOne ;
        m_cond = m_cond->next ;
      } // while

      m_tmpara = pos ;
      m_walk = copy ;
      shead = m_walk ;


      if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ||
           err == 20 || err == 21 ) {
        m_error = local ;
        return m_walk ;
      } // if
      else if ( err != -1 ) return m_walk ;

      return m_walk ;
    } // else
  } // Evaluate()

  void Finish( DATA * walk ) {

    if ( walk->down != NULL ) Finish( walk->down ) ;
    if ( walk->next != NULL ) Finish( walk->next ) ;
    walk->finish = true ;

  } // Finish()

  DATA * Lamb_do( DATA * m_walk, int & err ) { // 做lambda
    DATA * tmpara = NULL ;   // 紀錄binding的參數
    DATA * pos = m_tmpara ;
    DATA * walk = NULL ;
    DATA * fun = NULL ; // 參數的symbol
    DATA * now = NULL ;

    for ( DATA * h = m_para ; h != NULL ; h = h->down ) {
      if ( h->addr == m_walk->addr ) now = h ;
    } // for

    fun = now->next->down ; // 參數的symbol
    for ( DATA * p = m_walk->next ; fun->token != RIGHT ; p = p->next ) { // 接參數
      DATA * t = new DATA ;
      NewNode( t ) ;
      Copy( t, fun, fun->element ) ;
      t->next = new DATA ;
      NewNode( t->next ) ;
      t->next = CopyPointer( t->next, p ) ;
      t->next->next = NULL ;

      if ( walk == NULL ) {
        walk = t ;
        tmpara = walk ;
      } // if
      else {
        walk->down = t;
        walk = walk->down ;
      } // else

      fun = fun->next ;
    } // for


    if ( m_tmpara == NULL ) m_tmpara = tmpara ;
    else {
      DATA * t = tmpara ;
      while ( t->down != NULL ) t = t->down ;
      t->down = m_tmpara ;
      m_tmpara = tmpara ;
    } // else


    for ( fun = now->next->next ; fun != NULL ; fun = fun->next ) {
      m_cond = new DATA ;
      NewNode( m_cond ) ;
      m_cond = CopyPointer( m_cond, fun ) ;
      m_cond->next = NULL ;
      m_walk = m_cond ;
      
      DATA * copy = new DATA ;
      NewNode( copy ) ;
      copy = CopyPointer( copy, m_cond ) ;
      Semantics_sub( m_walk, copy, true, err, true ) ;
      if ( err != -1 ) {
        m_tmpara = pos ;
        m_walk = m_cond ;
        return m_walk ;
      } // if
    } // for

    m_tmpara = pos ;
    m_walk = m_cond ;
    return m_walk ;

  } // Lamb_do()

  bool CheckErr( DATA * m_walk, DATA * local, bool & isBound, bool & preDef,
                 bool if_cond, int level, int & err, bool back ) {  // ------------------------- 語意判斷
    DATA * p = NULL ;
    DATA * tmp = m_walk ;
    m_error = m_walk ;
    if ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ) preDef = true ;

    for ( DATA * t = m_walk ; t != NULL ; t = t->next ) { // 檢查EXP是不是list
      if ( t->token == DOT ) {
        err = 6 ;
        m_error = m_current ;
        return false ;
      } // if
    } // for

    if ( m_walk->token != SYMBOL && m_walk->token != QUOTE && m_walk->token != LEFT ) { // 第一個是原子
      m_walk->next = NULL ;
      err = 7 ;
      m_error = m_walk ;
      return false ;
    } // if
    else if ( m_walk->token == SYMBOL || m_walk->token == QUOTE ) {

      if ( !isBound && !m_walk->mean && !m_walk->finish ) {
        err = 5 ;
        m_walk->next = NULL ;
        m_error = m_walk ;
        return false ;
      } // if

      if ( m_walk->mean ) { // intenal func

        if ( ( if_cond || level != 1 ) &&
             ( strcmp( m_walk->element, "#<procedure clean-environment>" ) == 0 ||
               strcmp( m_walk->element, "#<procedure exit>" ) == 0 ||
               strcmp( m_walk->element, "#<procedure define>" ) == 0 ) ) {
          if ( strcmp( m_walk->element, "#<procedure clean-environment>" ) == 0 ) err = 8 ;
          if ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ) err = 9 ;
          if ( strcmp( m_walk->element, "#<procedure exit>" ) == 0 ) err = 10 ; // non top-level

          return false ;
        } // if
        else if ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure set!>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure let>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure cond>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure lambda>" ) == 0 ) { // 格式錯誤

          int num = 0 ;
          for ( p = m_walk->next ; p->next != NULL ; p = p->next )
            num++ ;


          if ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ) {
            bool inerr = false ;
            for ( DATA * b = m_function ; b != NULL ; b = b->down ) {
              if ( strcmp( b->element, m_walk->next->element ) == 0 && b->inter ) inerr = true ;
            } // for

            if ( ( m_walk->next->token == SYMBOL && num != 2 ) ||
                 ( m_walk->next->token != SYMBOL && m_walk->next->token != LEFT ) || inerr ) {
              err = 11 ;
              m_error = local ;
              return false ;
            } // if
            else if ( m_walk->next->token == LEFT ) {  // 判斷define function的參數要為symbol
              bool is_symbol = true ;
              for ( DATA * t = m_walk->next->down ; t->token != RIGHT && is_symbol ; t = t->next ) {
                if ( t->token != SYMBOL ) is_symbol = false ;
              } // for

              if ( !is_symbol ) {
                err = 11 ;
                m_error = local ;
                return false ;
              } // if
            } // else if
          } // if
          else if ( strcmp( m_walk->element, "#<procedure set!>" ) == 0 ) {  // *********************

            if ( m_walk->next->token != SYMBOL || m_walk->next->next->next != NULL  ) {
              err = 12 ;
              m_error = m_walk ;
              return false ;
            } // if
          } // else if
          else if ( strcmp( m_walk->element, "#<procedure lambda>" ) == 0 ) {  // ********************

            // step1. 檢查參數是否為symbol
            bool have = false ;
            for ( DATA * h = m_para ; h != NULL ; h = h->down ) {
              if ( h->addr == m_walk->addr ) have = true ;
            } // for

            if ( ! have ) {
              bool is_symbol = true ;
              
              if ( m_walk->next->token == NIL ) {
                if ( m_walk->next->next != NULL && m_walk->next->next->token == RIGHT ) is_symbol = false ;
                else is_symbol = true ;
              } // if
              else if ( m_walk->next->token != LEFT ) is_symbol = false ;
              else if ( m_walk->next->next != NULL && m_walk->next->next->token == RIGHT ) 
                is_symbol = false ;
              else {
                for ( DATA * t = m_walk->next->down ; t->token != RIGHT && is_symbol ; t = t->next ) {
                  if ( t->token != SYMBOL ) is_symbol = false ;
                } // for
              } // else

              if ( !is_symbol ) {
                err = 13 ;
                m_error = local ;
                return false ;
              } // if
            } // if
            else {
              // step2. 檢查參數個數
              int num = 0 ;
              char temp[20] = { '\0' } ;

              for ( p = m_walk->next ; p->next != NULL ; p = p->next )
                num++ ;

              bool find = false ;    // 判斷新function個數
              for ( DATA * fun = m_para ; !find && fun != NULL ; fun = fun->down ) {
                if ( strcmp( fun->element, m_walk->element ) == 0 && fun->addr == m_walk->addr ) {
                  find = true ;
                  for ( fun = fun->next->down ; fun->token != RIGHT ; fun = fun->next )
                    num-- ;

                  if ( num != 0 ) {
                    int i ;
                    for ( i = 12 ; i < strlen( m_walk->element )-1 ; i++ )
                      temp[i-12] = m_walk->element[i] ;

                    temp[i] = '\0' ;
                  } // if
                } // if
              } // for

              if ( strcmp( temp, "" ) != 0 ) {
                err = 16 ;
                strcpy( m_walk->element, temp ) ;
                for ( int i = 0 ; i < 20 ; i++ )
                  temp[i] = '\0' ;
                m_walk->next = NULL ;
                m_error = m_walk ;
                return false ;
              } // if
            } // else

          } // else if
          else if ( strcmp( m_walk->element, "#<procedure let>" ) == 0 ) {     // ***************
            bool trap = false ;

            // 找前端binding錯誤
            if ( m_walk->next->token == NIL ) ;
            else if ( m_walk->next->token == LEFT ) {
              for ( DATA * t = m_walk->next->down ; t->token != RIGHT && ! trap ; t = t->next ) {
                if ( t->token != LEFT ) trap = true ;
                else if ( t->down != NULL && t->down->token != SYMBOL ) trap = true ;
                else if ( t->down->next != NULL && t->down->next->next != NULL && 
                          t->down->next->next->token != RIGHT ) trap = true ;
              } // for
            } // else if
            else trap = true ;

            if ( m_walk->next->next->token == RIGHT ) trap = true ;

            if ( trap ) {
              err = 14 ;
              m_error = local ;
              return false ;
            } // if

            return true ;

          } // else if
          else if ( strcmp( m_walk->element, "#<procedure cond>" ) == 0 ) {
            num = 0 ;
            for ( p = m_walk->next ; strcmp( p->element, ")" ) != 0 ; p = p->next ) {
              num++ ;
              if ( p->token != LEFT ) {
                err = 15 ;
                return false ;
              } // if
              else {
                int count = 0 ;
                for ( DATA * tmp = p->down ; tmp->token != RIGHT ; tmp = tmp->next )
                  count++ ;

                if ( count < 2 ) {
                  err = 15 ;
                  return false ;
                } // if
              } // else
            } // for

            if ( num == 0 ) {
              err = 15 ;
              return false ;
            } // if
          } // else if

          return true ;
        } // else if
        else if ( strcmp( m_walk->element, "#<procedure if>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure and>" ) == 0 ||
                  strcmp( m_walk->element, "#<procedure or>" ) == 0 ) { // 數量錯誤
          int num = 0 ;
          for ( p = m_walk->next ; p->next != NULL ; p = p->next )
            num++ ;

          if ( strcmp( m_walk->element, "#<procedure if>" ) == 0 &&
               ( num != 2 && num != 3 ) ) {
            strcpy( m_walk->element, "if" ) ;
            m_walk->next = NULL ;
            err = 16 ;
            m_error = m_walk ;
            return false ;
          } // if
          else if ( num < 2 ) {
            if ( strcmp( m_walk->element, "#<procedure and>" ) == 0 ) strcpy( m_walk->element, "and" ) ;
            else  strcpy( m_walk->element, "or" ) ;
            m_walk->next = NULL ;
            err = 16 ;
            m_error = m_walk ;
            return false ;
          } // else if

          return true ;
        } // else if
        else if ( ! ( strcmp( m_walk->element, "#<procedure define>" ) == 0 ||
                      strcmp( m_walk->element, "#<procedure let>" ) == 0 ||
                      strcmp( m_walk->element, "#<procedure cond>" ) == 0 ) ) { // 數量錯誤
          int num = 0 ;
          char temp[20] = { '\0' } ;

          for ( p = m_walk->next ; p->next != NULL ; p = p->next )
            num++ ;

          if ( strcmp( m_walk->element, "#<procedure cons>" ) == 0 && num != 2 )
            strcpy( temp, "cons" ) ;
          else if ( strcmp( m_walk->element, "#<procedure list>" ) == 0 && num < 0 )
            strcpy( temp, "list" ) ;
          else if ( strcmp( m_walk->element, "#<procedure quote>" ) == 0 && num > 1 )
            strcpy( temp, "quote" ) ;
          else if ( strcmp( m_walk->element, "#<procedure car>" ) == 0 && num != 1 )
            strcpy( temp, "car" ) ;
          else if ( strcmp( m_walk->element, "#<procedure cdr>" ) == 0 && num != 1 )
            strcpy( temp, "cdr" ) ;
          else if ( strcmp( m_walk->element, "#<procedure +>" ) == 0 && num < 2 )
            strcpy( temp, "+" ) ;
          else if ( strcmp( m_walk->element, "#<procedure ->" ) == 0 && num < 2 )
            strcpy( temp, "-" ) ;
          else if ( strcmp( m_walk->element, "#<procedure *>" ) == 0 && num < 2 )
            strcpy( temp, "*" ) ;
          else if ( strcmp( m_walk->element, "#<procedure />" ) == 0 && num < 2 )
            strcpy( temp, "/" ) ;
          else if ( strcmp( m_walk->element, "#<procedure not>" ) == 0 && num != 1 )
            strcpy( temp, "not" ) ;
          else if ( strcmp( m_walk->element, "#<procedure and>" ) == 0 && num < 2 )
            strcpy( temp, "and" ) ;
          else if ( strcmp( m_walk->element, "#<procedure or>" ) == 0 && num < 2 )
            strcpy( temp, "or" ) ;
          else if ( strcmp( m_walk->element, "#<procedure >>" ) == 0 && num < 2 )
            strcpy( temp, ">" ) ;
          else if ( strcmp( m_walk->element, "#<procedure <>" ) == 0 && num < 2 )
            strcpy( temp, "<" ) ;
          else if ( strcmp( m_walk->element, "#<procedure >=>" ) == 0 && num < 2 )
            strcpy( temp, ">=" ) ;
          else if ( strcmp( m_walk->element, "#<procedure <=>" ) == 0 && num < 2 )
            strcpy( temp, "<=" ) ;
          else if ( strcmp( m_walk->element, "#<procedure =>" ) == 0 && num < 2 )
            strcpy( temp, "=" ) ;
          else if ( strcmp( m_walk->element, "#<procedure string-append>" ) == 0 && num < 2 )
            strcpy( temp, "string-append" ) ;
          else if ( strcmp( m_walk->element, "#<procedure string>?>" ) == 0 && num < 2 )
            strcpy( temp, "string>?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure string<?>" ) == 0 && num < 2 )
            strcpy( temp, "string<?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure string=?>" ) == 0 && num < 2 )
            strcpy( temp, "string=?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure eqv?>" ) == 0 && num != 2 )
            strcpy( temp, "eqv?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure equal?>" ) == 0 && num != 2 )
            strcpy( temp, "equal?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure begin>" ) == 0 && num <= 0 )
            strcpy( temp, "begin" ) ;
          else if ( strcmp( m_walk->element, "#<procedure if>" ) == 0 && num > 3 )
            strcpy( temp, "if" ) ;
          else if ( strcmp( m_walk->element, "#<procedure atom?>" ) == 0 && num != 1 )
            strcpy( temp, "atom?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure pair?>" ) == 0 && num != 1 )
            strcpy( temp, "pair?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure list?>" ) == 0 && num != 1 )
            strcpy( temp, "list?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure null?>" ) == 0 && num != 1 )
            strcpy( temp, "null?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure integer?>" ) == 0 && num != 1 )
            strcpy( temp, "integer?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure real?>" ) == 0 && num != 1 )
            strcpy( temp, "real?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure number?>" ) == 0 && num != 1 )
            strcpy( temp, "number? " ) ;
          else if ( strcmp( m_walk->element, "#<procedure string?>" ) == 0 && num != 1 )
            strcpy( temp, "string?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure boolean?>" ) == 0 && num != 1 )
            strcpy( temp, "boolean?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure symbol?>" ) == 0 && num != 1 )
            strcpy( temp, "symbol?" ) ;
          else if ( strcmp( m_walk->element, "#<procedure exit>" ) == 0 && num != 0 )
            strcpy( temp, "exit" ) ;
          else {

            bool find = false ;    // 判斷新function個數
            for ( DATA * fun = m_para ; !find && fun != NULL ; fun = fun->down ) {
              if ( strcmp( fun->element, m_walk->element ) == 0 ) {
                find = true ;
                for ( fun = fun->next->down ; fun->token != RIGHT ; fun = fun->next )
                  num-- ;

                if ( num != 0 ) {
                  int i ;
                  for ( i = 12 ; i < strlen( m_walk->element )-1 ; i++ )
                    temp[i-12] = m_walk->element[i] ;

                  temp[i] = '\0' ;
                } // if
              } // if
            } // for
          } // else

          if ( strcmp( temp, "" ) != 0 ) {
            err = 16 ;
            strcpy( m_walk->element, temp ) ;
            for ( int i = 0 ; i < 20 ; i++ )
              temp[i] = '\0' ;
            m_walk->next = NULL ;
            m_error = m_walk ;
            return false ;
          } // if

          return true ;
        } // else if
      } // if

      else {
        err = 7 ;
        m_walk->next = NULL ;
        m_error = m_walk ;
        return false ;
      } // else
    } // else if
    else if ( back && m_walk->token == LEFT && m_walk->down != NULL ) {
      m_walk->next = NULL ;
      err = 7 ;
      m_error = m_walk ;
      return false ;
    } // else if
    else { // (...)
      isBound = true ;
      return true ;
    } // else

    return true ;
  } // CheckErr()

  bool CheckErr2( DATA * m_walk, DATA * shead, DATA * local, int & err ) {     // 型別錯誤
    if ( strcmp( shead->element, "#<procedure define>" ) == 0 || // ERROR (xxx with incorrect argument type)
         strcmp( shead->element, "#<procedure set!>" ) == 0 ||
         strcmp( shead->element, "#<procedure let>" ) == 0 ||
         strcmp( shead->element, "#<procedure cond>" ) == 0 ||
         strcmp( shead->element, "#<procedure lambda>" ) == 0 ) {

      if ( strcmp( shead->element, "#<procedure cond>" ) == 0 ) {
        if ( strcmp( m_walk->element, "(" ) != 0 && strcmp( m_walk->element, ")" ) != 0 ) {
          err = 17 ;
          strcpy( m_temp->element, "cond" ) ;
          m_error = m_walk ;
          return false ;
        } // if
      } // if

      return true ;
    } // if
    else if ( strcmp( shead->element, "#<procedure if>" ) == 0 ||  // 型別錯誤
              strcmp( shead->element, "#<procedure and>" ) == 0 ||
              strcmp( shead->element, "#<procedure or>" ) == 0 ) {

      if ( strcmp( shead->element, "#<procedure and>" ) == 0 && m_walk->token == NIL ) return false ;
      else if ( strcmp( shead->element, "#<procedure or>" ) == 0 && m_walk->token != NIL ) return false ;
      else if ( strcmp( shead->element, "#<procedure if>" ) == 0 ) {

        if ( m_walk->token == NIL ) {
          m_walk->next->token = T ;
          m_walk->next->down = NULL ;
        } // if

        return true ;
      } // else if
      else return true ;
    } // else if
    else if ( ! ( strcmp( shead->element, "#<procedure define>" ) == 0 ||    // 型別錯誤
                  strcmp( shead->element, "#<procedure let>" ) == 0 ||
                  strcmp( shead->element, "#<procedure cond>" ) == 0 ||
                  strcmp( shead->element, "#<procedure lambda>" ) == 0 ) ) {
      char temp[20] = { '\0' } ;

      if ( strcmp( shead->element, "#<procedure car>" ) == 0 && m_walk->token != LEFT )
        strcpy( temp, "car" ) ;
      else if ( strcmp( shead->element, "#<procedure cdr>" ) == 0 && m_walk->token != LEFT )
        strcpy( temp, "cdr" ) ;
      else if ( strcmp( shead->element, "#<procedure +>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "+" ) ;
      else if ( strcmp( shead->element, "#<procedure ->" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "-" ) ;
      else if ( strcmp( shead->element, "#<procedure *>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "*" ) ;
      else if ( strcmp( shead->element, "#<procedure />" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "/" ) ;
      else if ( strcmp( shead->element, "#<procedure >>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, ">" ) ;
      else if ( strcmp( shead->element, "#<procedure <>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "<" ) ;
      else if ( strcmp( shead->element, "#<procedure >=>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, ">=" ) ;
      else if ( strcmp( shead->element, "#<procedure <=>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "<=" ) ;
      else if ( strcmp( shead->element, "#<procedure =>" ) == 0 &&
                ( m_walk->token != FLOAT && m_walk->token != INT ) ) strcpy( temp, "=" ) ;
      else if ( strcmp( shead->element, "#<procedure string-append>" ) == 0 && m_walk->token != STRING )
        strcpy( temp, "string-append" ) ;
      else if ( strcmp( shead->element, "#<procedure string>?>" ) == 0 && m_walk->token != STRING )
        strcpy( temp, "string>?" ) ;
      else if ( strcmp( shead->element, "#<procedure string<?>" ) == 0 && m_walk->token != STRING )
        strcpy( temp, "string<?" ) ;
      else if ( strcmp( shead->element, "#<procedure string=?>" ) == 0 && m_walk->token != STRING )
        strcpy( temp, "string=?" ) ;
      if ( strcmp( temp, "" ) != 0 ) {
        strcpy( m_temp->element, temp ) ;
        err = 17 ;
        m_error = m_walk ;
        m_error->next = NULL ;
        return false ;
      } // if

      return true ;
    } // else if

    return true ;
  } // CheckErr2()

  DATA * Preprocesor( DATA * m_walk, bool Def, bool & isBound ) {
    bool is_SYMBOL = false ;
    bool b = false ;

    if ( m_walk->token == SYMBOL || m_walk->token == QUOTE ) is_SYMBOL = true ;
    else is_SYMBOL = false ;

    for ( DATA * fun = m_tmpara ; fun != NULL && is_SYMBOL ; fun = fun->down ) {
      if ( strcmp( m_walk->element, fun->element ) == 0 ) {
        b = true ;
        DATA * theFunction = fun->next ;
        if ( fun->next != NULL && ! fun->next->finish ) theFunction = Findfun( fun->next ) ;
        DATA * temp = m_walk->next ;
        if ( fun->next != NULL ) m_walk = CopyPointer( m_walk, theFunction ) ;
        m_walk->next = temp ;
      } // if
    } // for

    for ( DATA * fun = m_function ; fun != NULL && is_SYMBOL && !b ; fun = fun->down ) {
      if ( strcmp( m_walk->element, fun->element ) == 0 ) {

        b = true ;
        DATA * theFunction = fun->next ;
        if ( ! fun->next->finish ) theFunction = Findfun( fun->next ) ;
        DATA * temp = m_walk->next ;
        m_walk = CopyPointer( m_walk, theFunction ) ;
        m_walk->next = temp ;


      } // if
    } // for

    if ( is_SYMBOL && !b ) {
      m_error = m_walk ;
      isBound = false ;
    } // if

    if ( ( !is_SYMBOL && !b ) || ( is_SYMBOL && b ) ) isBound = true ;
    return m_walk ;
  } // Preprocesor()

  DATA * Findfun( DATA * m_walk ) {
    for ( DATA * fun = m_function ; fun != NULL ; fun = fun->down ) {
      if ( strcmp( m_walk->element, fun->element ) == 0 ) {

        if ( strcmp( fun->next->element, "(" ) == 0 || fun->next->element[0] == '\"' )
          return fun->next ;
        else return Findfun( fun->next ) ;
      } // if
    } // for

    return m_walk ;
  } // Findfun()

  DATA * For_Def( DATA * m_walk ) {
    bool b = false ;

    if ( strcmp( m_walk->element, "quote" ) == 0 ) return m_walk ;
    if ( strcmp( m_walk->element, "lambda" ) == 0 ) return m_walk ;
    if ( strcmp( m_walk->element, "let" ) == 0 ) {
      return m_walk ;
    } // if

    if ( m_walk->down != NULL ) m_walk->down = For_Def( m_walk->down ) ;
    if ( m_walk->next != NULL ) m_walk->next = For_Def( m_walk->next ) ;

    return m_walk = Preprocesor( m_walk, false, b ) ;
  } // For_Def()

  void Define( DATA * m_walk ) {
    DATA * t = m_current->down->next->next ;
    while ( t->next->token != RIGHT ) t = t->next ;
    t->next = NULL ;           // 把最後面多餘的 ')' 消掉

    DATA * tmp = m_function ;
    DATA * tmp2 = tmp ;        // tmp2指向tmp的上一個
    bool done = false ;



    if ( m_current->down->next->token != LEFT ) {   // define symbol

      for ( ; tmp != NULL && !done ; tmp = tmp->down ) {
        if ( strcmp( tmp->element, m_current->down->next->element ) == 0 ) {  // 找到相同的function -> 覆寫
          tmp->next = m_walk->next->next ;
          done = true ;
        } // if

        if ( tmp != m_function ) tmp2 = tmp2->down ;
      } // for

      if ( !done ) {
        DATA * h = new DATA ;
        NewNode( h ) ;
        Copy( h, m_current->down->next, m_current->down->next->element ) ;
        h->next = m_walk->next->next ;
        tmp2->down = h ;
      } // if
    } // if
    else {                                     // define function
      DATA * y = m_current->down->next->down ; // SYM
      for ( DATA * h = y->next ; h != NULL ; h = h->down ) {
        h->down = h->next ;
        h->next = NULL;
      } // for

      m_tmpara = y->next ;

      For_Def( m_current->down->next->next ) ;

      m_tmpara = NULL ;
      for ( DATA * h = y->next ; h != NULL ; h = h->next ) {
        h->next = h->down ;
        h->down = NULL ;
      } // for

      // step1. 先綁定m_function
      for ( ; tmp != NULL && !done ; tmp = tmp->down ) {
        if ( strcmp( tmp->element, y->element ) == 0 ) {  // 找到相同的function
          tmp->next = new DATA ;
          NewNode( tmp->next ) ;
          tmp->next->token = SYMBOL ;
          // tmp->next->inter = true ;
          tmp->next->mean = true ;
          string s = string( tmp->element ) ;
          string t = "#<procedure " + s + ">" ;
          strcpy( tmp->next->element, t.c_str() ) ;

          done = true ;
        } // if

        if ( tmp != m_function ) tmp2 = tmp2->down ;
      } // for

      if ( !done ) {
        tmp2->down = new DATA ;
        NewNode( tmp2->down ) ;
        Copy( tmp2->down, m_current->down->next->down, m_current->down->next->down->element ) ;

        tmp2->down->next = new DATA ;
        NewNode( tmp2->down->next ) ;
        tmp2->down->next->token = SYMBOL ;
        // tmp2->down->next->inter = true ;
        tmp2->down->next->mean = true ;
        string s = string( tmp2->down->element ) ;
        string t = "#<procedure " + s + ">" ;
        strcpy( tmp2->down->next->element, t.c_str() ) ;
      } // if

      // step2. 綁定m_para
      bool isBound = false ;
      DATA * fun = y ;
      DATA * para = m_current->down->next ;
      done = false ;
      y = Preprocesor( y, false, isBound ) ;
      para->down = y->next ;
      y->next = para ;


      if ( m_para == NULL ) m_para = y ;
      else {
        for ( fun = m_para ; fun != NULL ; fun = fun->down ) {
          if ( strcmp( fun->element, y->element ) == 0 ) {
            Copy( fun, y, y->element ) ;
            fun->next = y->next ;
            done = true ;
          } // if
        } // for

        if ( !done ) {
          fun = m_para ;
          while ( fun->down != NULL ) fun = fun->down ;
          fun->down = y ;
        } // if
      } // else

    } // else
  } // Define()

  DATA * CopyPointer( DATA * walk, DATA * fun ) {  // ----- 深層複製pointer
    if ( fun != NULL ) {
      Copy( walk, fun, fun->element ) ;

      if ( fun->down != NULL ) {
        walk->down = new DATA ;
        NewNode( walk->down ) ;
        walk->down = CopyPointer( walk->down, fun->down ) ;
      } // if

      if ( fun->next != NULL ) {
        walk->next = new DATA ;
        NewNode( walk->next ) ;
        walk->next = CopyPointer( walk->next, fun->next ) ;
      } // if
    } // if

    return walk ;
  } // CopyPointer()

  DATA * Arithmetic( DATA * m_walk, char op[256], int & err ) {  // -- 四則運算 + - * /
    bool isFloat = false, been = false ;
    float float_outcome = 0.0 ;
    int int_outcome = 0 ;

    for ( DATA * tmp = m_walk ; tmp != NULL ; tmp = tmp->next )
      if ( tmp->token == FLOAT ) isFloat = true ;  // 有浮點數 轉為float

    for ( DATA * tmp = m_walk->next ; strcmp( tmp->element, ")" ) != 0  ; tmp = tmp->next ) {
      if ( strcmp( op, "#<procedure +>" ) == 0 ) {
        if ( isFloat ) float_outcome = float_outcome + atof( tmp->element ) ;
        else int_outcome = int_outcome + atoi( tmp->element ) ;
      } // if
      else if ( strcmp( op, "#<procedure ->" ) == 0 ) {

        if ( isFloat ) {
          if ( float_outcome == 0.0 ) float_outcome = atof( tmp->element ) ;
          else float_outcome = float_outcome - atof( tmp->element ) ;
        } // if
        else {
          if ( !been ) {
            been = true ;
            int_outcome = atoi( tmp->element ) ;
          } // if
          else int_outcome = int_outcome - atoi( tmp->element ) ;
        } // else
      } // else if
      else if ( strcmp( op, "#<procedure *>" ) == 0 ) {
        if ( isFloat ) {
          if ( float_outcome == 0.0 ) float_outcome = atof( tmp->element ) ;
          else float_outcome = float_outcome * atof( tmp->element ) ;
        } // if
        else {
          if ( ! been ) {
            been = true ;
            int_outcome = atoi( tmp->element ) ;
          } // if
          else int_outcome = int_outcome * atoi( tmp->element ) ;
        } // else
      } // else if
      else if ( strcmp( op, "#<procedure />" ) == 0 ) {
        if ( isFloat ) {
          if ( !been ) {
            float_outcome = atof( tmp->element ) ;
            been = true ;
          } // if
          else {

            if ( tmp != m_walk->next && atof( tmp->element ) == 0.0 ) err = 19 ;
            else float_outcome = float_outcome / atof( tmp->element ) ;
          } // else
        } // if
        else {
          if ( !been ) {
            been = true ;
            int_outcome = atoi( tmp->element ) ;
          } // if
          else {
            if ( tmp != m_walk->next && atoi( tmp->element ) == 0 ) err = 19 ;
            else int_outcome = int_outcome / atoi( tmp->element ) ;
          } // else
        } // else
      } // else if
    } // for

    DATA * temp = new DATA ;
    NewNode( temp ) ;
    if ( isFloat ) {
      temp->token = FLOAT ;
      sprintf( temp->element, "%.3f", float_outcome ) ;
    } // if
    else {
      temp->token = INT ;
      sprintf( temp->element, "%d", int_outcome ) ;
    } // else

    return temp ;
  } // Arithmetic()

  DATA * LogicOperation( DATA * m_walk ) {  // ------------ 邏輯計算 and not or
    DATA * temp = new DATA ;
    NewNode( temp ) ;
    strcpy( temp->element, "nil" ) ;
    temp->token = NIL ;   // 先預設成 NIL(false)

    if ( strcmp( m_walk->element, "#<procedure and>" ) == 0 ) {
      bool have_nil = false ;
      DATA * tmp = m_walk->next ;
      for ( ; strcmp( tmp->next->element, ")" ) != 0 ; tmp = tmp->next )
        if ( tmp->token == NIL ) have_nil = true ;

      if ( !have_nil ) Copy( temp, tmp, tmp->element ) ;
    } // if
    else if ( strcmp( m_walk->element, "#<procedure or>" ) == 0 ) {
      bool have_t = false ;
      DATA * tmp = m_walk->next ;
      for ( ; strcmp( tmp->element, ")" ) != 0 && ! have_t ; tmp = tmp->next ) {
        if ( tmp->token != NIL ) {
          have_t = true ;
          Copy( temp, tmp, tmp->element ) ;
        } // if
      } // for

    } // else if
    else if ( strcmp( m_walk->element, "#<procedure not>" ) == 0 )
      if ( m_walk->next->token == NIL ) temp->token = T ;

    if ( temp->token == T ) strcpy( temp->element, "#t" ) ;

    return temp ;
  } // LogicOperation()

  DATA * JudgmentType( DATA * m_walk ) {  // -------------- 判斷型別 atom? / integer?
    DATA * temp = new DATA ;
    NewNode( temp ) ;
    strcpy( temp->element, "nil" ) ;
    temp->token = NIL ;   // 先預設成 NIL(false)

    if ( strcmp( m_walk->element, "#<procedure null?>" ) == 0 ) {
      if ( m_walk->next->token == NIL ) temp->token = T ;
    } // if

    else if ( strcmp( m_walk->element, "#<procedure integer?>" ) == 0 ) {
      if ( m_walk->next->token == INT ) temp->token = T ;
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure string?>" ) == 0 ) {
      if ( m_walk->next->token == STRING ) temp->token = T ;
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure symbol?>" ) == 0 ) {
      if ( m_walk->next->token == SYMBOL ) temp->token = T ;
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure list?>" ) == 0 ) {
      bool rList = false ;
      if ( m_walk->next->token == NIL ) temp->token = T ;
      else if ( strcmp( m_walk->next->element, "(" ) == 0 ) {

        for ( DATA * tmp = m_walk->next->down ; tmp != NULL ; tmp = tmp->next )
          if ( tmp->token == DOT ) rList = true ;

        if ( !rList ) temp->token = T ;
      } // else if
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure boolean?>" ) == 0 ) {
      if ( m_walk->next->token == NIL || m_walk->next->token == T ) temp->token = T ;
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure real?>" ) == 0 ||
              strcmp( m_walk->element, "#<procedure number?>" ) == 0 ) {
      if ( m_walk->next->token == INT || m_walk->next->token == FLOAT ) temp->token = T ; // real = number
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure atom?>" ) == 0 ) {
      if ( m_walk->next->token == INT || m_walk->next->token == FLOAT || m_walk->next->token == STRING ||
           m_walk->next->token == NIL || m_walk->next->token == T || m_walk->next->token == SYMBOL )
        temp->token = T ;
    } // else if

    else if ( strcmp( m_walk->element, "#<procedure pair?>" ) == 0 ) {
      if ( strcmp( m_walk->next->element, "(" ) == 0 ) temp->token = T ;
    } // else if

    if ( temp->token == T ) strcpy( temp->element, "#t" ) ;

    return temp ;
  } // JudgmentType()

  bool CheckEqual( DATA * one, DATA * two ) {  // --------- 檢查equal的遞迴式
    if ( one == NULL && two == NULL ) return true ;
    else if ( one == NULL || two == NULL ) return false ;
    else if ( strcmp( one->element, two->element ) != 0 ) return false ;

    if ( CheckEqual( one->down, two->down ) ) {
      if ( CheckEqual( one->next, two->next ) && strcmp( one->element, two->element ) == 0 ) return true ;
      else return false ;
    } // if

    else return false ;
  } // CheckEqual()

  DATA * Equal( DATA * m_walk ) {  // --------------------- 判斷 eqv? / equal?
    DATA * temp = new DATA ;
    NewNode( temp ) ;
    strcpy( temp->element, "nil" ) ;
    temp->token = NIL ;   // 先預設成 NIL(false)

    DATA * one = m_walk->next ;
    DATA * two = m_walk->next->next ;

    if ( strcmp( m_walk->element, "#<procedure equal?>" ) == 0 ||
         strcmp( m_walk->element, "#<procedure eqv?>" ) == 0 ) {

      if ( one->token == LEFT && CheckEqual( one->down, two->down ) )
        temp->token = T ;
      else if ( one->token != LEFT && strcmp( one->element, two->element ) == 0 )
        temp->token = T ;

    } // if

    one->next = NULL ;
    two->next = NULL ;

    if ( strcmp( m_walk->element, "#<procedure eqv?>" ) == 0 &&
         ( ( one->token == INT && two->token == INT ) || ( one->token == FLOAT && two->token == FLOAT ) ||
           ( one->token == T && two->token == T ) || ( one->token == NIL && two->token == NIL ) ) ) {
      strcpy( temp->element, "#t" ) ;
      return temp ;
    } // if
    else if ( strcmp( m_walk->element, "#<procedure eqv?>" ) == 0 && !Address( one, two ) ) {
      temp->token = NIL ;
      strcpy( temp->element, "nil" ) ;
    } // else if
    else if ( temp->token == T ) strcpy( temp->element, "#t" ) ;

    return temp ;
  } // Equal()

  bool Address( DATA * one, DATA * two ) {  // --------- 檢查eqv?的遞迴式
  
    if ( one == NULL && two == NULL ) return true;
    else if ( one == NULL || two == NULL ) return  false;
    else if ( one->addr != two->addr ) return  false;

    if ( Address( one->down, two->down ) ) {
      if ( Address( one->next, two->next ) && one->addr == two->addr ) return  true;
      else return  false;
    } // if

    else return  false;
  } // Address()

  DATA * Compare( DATA * m_walk, char op[256] ) {  // ----- 大於小於的比較 >= / <= / string>?
    DATA * temp = new DATA ;
    NewNode( temp ) ;
    strcpy( temp->element, "#t" ) ;
    temp->token = T ;   // 先預設成 T(true)
    bool right = true ;

    if ( strcmp( op, "#<procedure >>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( atof( tmp->element ) <= atof( tmp->next->element ) )
          right = false ;
      } // for
    } // if
    else if ( strcmp( op, "#<procedure <>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( atof( tmp->element ) >= atof( tmp->next->element ) )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure >=>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( atof( tmp->element ) < atof( tmp->next->element ) )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure <=>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( atof( tmp->element ) > atof( tmp->next->element ) )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure =>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( atof( tmp->element ) != atof( tmp->next->element ) )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure string>?>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( strcmp( tmp->element, tmp->next->element ) <= 0 )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure string<?>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( strcmp( tmp->element, tmp->next->element ) >= 0 )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure string=?>" ) == 0 ) {
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->next->element, ")" ) != 0  ; tmp = tmp->next ) {
        if ( strcmp( tmp->element, tmp->next->element ) != 0 )
          right = false ;
      } // for
    } // else if
    else if ( strcmp( op, "#<procedure string-append>" ) == 0 ) {
      char str[256] = {'\0'} ;
      for ( DATA * tmp = m_walk->next ; strcmp( tmp->element, ")" ) != 0  ; tmp = tmp->next ) {
        int len = strlen( tmp->element ) ;  // 去除多餘的 ""
        for ( int i = 0 ; i < len - 1 ; i++ ) {
          tmp->element[i] = tmp->element[i+1] ;
        } // for

        tmp->element[len - 2] = '\0' ;
        strcat( str, tmp->element ) ;
      } // for

      int len = strlen( str ) ;               // 在連接好的字串前後加 ""
      for ( int i = len ; i > 0 ; i-- ) {
        str[i] = str[i-1];
      } // for

      str[0] = '\"' ;
      str[len+1] = '\"' ;
      str[len+2] = '\0' ;
      temp->token = STRING ;
      strcpy( temp->element, str ) ;
    } // else if

    if ( !right && strcmp( op, "#<procedure string-append>" ) != 0 ) temp->token = NIL ;
    if ( temp->token == NIL ) strcpy( temp->element, "nil" ) ;
    return temp ;
  } // Compare()

  DATA * Peek_cond( DATA * m_walk, int & err, DATA * local ) {
    bool printDirectly = false, eqv = false, preDef = false ;
    bool eLse = false, if_cond = false, isBound = false ;
    DATA * copy ; // 複製一份cond以下的程式碼
    DATA * tmp2 = NULL ;
    DATA * pos ;
    
    for ( DATA * tmp = m_walk ; strcmp( tmp->element, ")" ) != 0 ; tmp = tmp->next ) { // 檢查cond以下第一個判斷式
      if ( strcmp( tmp->down->element, "else" ) == 0 && tmp->next->token == RIGHT ) { // 若是else則直接做
        m_cond = tmp->down->next ;
        while ( m_cond->token != RIGHT ) {
          pos = m_cond->next ;
          m_cond->next = NULL ;
          tmp2 = m_cond ;
          
          copy = new DATA ;
          NewNode( copy ) ;
          copy = CopyPointer( copy, m_cond ) ;
          Semantics_sub( tmp2, copy, true, err, true ) ;
          // if ( err != -1 ) return m_walk ;
          if ( pos->token == RIGHT ) copy = m_cond ;
          m_cond->next = pos ;
          m_cond = m_cond->next ;

          if ( ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) ) {
            m_error = local ;
            return m_walk ;
          } // if
          else if ( err == 18 && pos->token != RIGHT ) err = -1 ;
          else if ( err != -1 ) return m_walk ;
        } // while

        return copy ;
      } // if

      m_cond = tmp->down ;
      pos = m_cond->next ;
      m_cond->next = NULL ;
      tmp2 = m_cond ;
      
      copy = new DATA ;
      NewNode( copy ) ;
      copy = CopyPointer( copy, m_cond ) ;
      Semantics_sub( tmp2, copy, true, err, true ) ;
      // if ( err != -1 ) return m_walk ;
      if ( ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) ) {
        m_error = local ;
        return m_walk ;
      } // if
      else if ( err != -1 ) return m_walk ;
      m_cond->next = pos ;
      tmp->down = m_cond ;

      if ( tmp->down->token != NIL ) { // 開做
        m_cond = tmp->down->next ;
        while ( m_cond->token != RIGHT ) {
          pos = m_cond->next ;
          m_cond->next = NULL ;
          tmp2 = m_cond ;
          
          copy = new DATA ;
          NewNode( copy ) ;
          copy = CopyPointer( copy, m_cond ) ;
          Semantics_sub( tmp2, copy, true, err, true ) ;
          // if ( err != -1 ) return m_walk ;
          if ( ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) ) {
            m_error = copy ;
            return m_walk ;
          } // if
          else if ( err == 18 && pos->token != RIGHT ) err = -1 ;
          else if ( err != -1 ) return m_walk ;

          if ( pos->token == RIGHT ) copy = m_cond ;
          m_cond->next = pos ;
          m_cond = m_cond->next ;
        } // while

        return copy ;
      } // if
    } // for

    err = 18 ;
    m_coda = 1 ;
    m_error = local ;
    return m_walk ;
  } // Peek_cond()

  DATA * Peek_if( DATA * m_walk, int & err, DATA * local ) {
    bool printDirectly = false, eqv = false, preDef = false ;
    bool eLse = false, if_cond = false, isBound = false ;
    DATA * copy ; // 複製一份if後以下的程式碼
    DATA * tmp2 = NULL ;
    DATA * pos ;

    m_cond = m_walk ;
    pos = m_walk->next ;
    m_cond->next = NULL ;
    tmp2 = m_cond ;
    copy = new DATA ;
    NewNode( copy ) ;
    copy = CopyPointer( copy, m_cond ) ;
    
    Semantics_sub( tmp2, copy, true, err, true ) ;
    tmp2 = m_cond ;

    // if ( err != -1 ) return m_walk ;
    if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
      if ( m_error == NULL ) m_error = copy ;
      return m_walk ;
    } // if
    else if ( err != -1 ) return m_walk ;

    m_cond->next = pos ;

    if ( m_cond->token != NIL ) m_cond = m_cond->next ;
    else m_cond = m_cond->next->next ;

    if ( m_cond->token == RIGHT ) {
      err = 18 ;
      m_coda = 1 ;
      return m_walk ;
    } // if

    m_cond->next = NULL ;
    tmp2 = m_cond ;
    copy = new DATA ;
    NewNode( copy ) ;
    copy = CopyPointer( copy, m_cond ) ;
    Semantics_sub( tmp2, copy, true, err, true ) ;
    tmp2 = m_cond ;
    // if ( err != -1 ) return m_walk ;
    // if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 || err == 18 ) {
    if ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) {
      if ( m_error == NULL ) m_error = copy ;
      return m_walk ;
    } // if
    else if ( err != -1 ) return m_walk ;

    return m_cond ;
  } // Peek_if()

  DATA * Peek_let( DATA * m_walk, int & err, DATA * local ) {
    bool printDirectly = false, preDef = false, isBound = false ;
    DATA * walk ;
    DATA * pos = m_tmpara ;
    DATA * tmpara = NULL ;
    DATA * future = NULL ;
    DATA * outcome = NULL ;
    DATA * copy = NULL ;
    if ( m_walk->token == NIL ) ;
    else {
      for ( walk = m_walk->down ; walk->token != RIGHT ; walk = walk->next ) { // binding
        DATA * t = new DATA ;
        NewNode( t ) ;
        Copy( t, walk->down, walk->down->element ) ;

        m_cond = walk->down->next ;
        walk->down->next = NULL ;
        m_cond->next = NULL ;
        outcome = m_cond ;
        
        
        Semantics_sub( outcome, copy, true, err, false ) ;
        outcome = m_cond ;
        if ( ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) ) {
          m_error = local ;
          return m_walk ;
        } // if
        else if ( err != -1 ) return m_walk ;

        t->next = m_cond ;
        t->next->next = NULL ;

        if ( tmpara == NULL ) tmpara = t ;
        else {
          t->down = tmpara ;
          tmpara = t ;
        } // else
      } // for
    } // else

    DATA * t = tmpara ;
    while ( tmpara != NULL && t->down != NULL ) t = t->down; // tmpara 接到 m_tmpara
    if ( tmpara != NULL ) {
      t->down = m_tmpara ;
      m_tmpara = tmpara ;
    } // if

    for ( m_walk = m_walk->next ; m_walk->token != RIGHT ; m_walk = m_walk->next ) {

      future = m_walk->next ;
      m_walk->next = NULL ;
      m_cond = m_walk ;
      copy = new DATA ;
      NewNode( copy ) ;
      copy = CopyPointer( copy, m_cond ) ;
      Semantics_sub( m_walk, copy, true, err, false ) ;
      m_walk = m_cond ;

      if ( ( err == 11 || err == 12 || err == 13 || err == 14 || err == 15 ) ) {
        if ( m_error == NULL ) m_error = copy ;
        m_tmpara = pos ;
        return m_walk ;
      } // if
      else if ( err != -1 ) {
        m_tmpara = pos ;
        return m_walk ;
      } // else if

      if ( future->token == RIGHT ) outcome = m_walk ;
      m_walk->next = future ;
    } // for

    m_tmpara = pos ;
    outcome->next = NULL ;
    return outcome ;
  } // Peek_let()

  DATA * Begin( DATA * m_walk ) {  // --------------------- begin 功能(?)
    DATA * temp = new DATA ;
    NewNode( temp ) ;
    strcpy( temp->element, "nil" ) ;
    temp->token = NIL ;   // 先預設成 NIL(false)

    for ( DATA * t = m_walk ; t->next != NULL ; t = t->next ) {
      if ( strcmp( t->element, ")" ) != 0 ) temp = t ;
    } // for

    temp->next = NULL ;
    return temp ;
  } // Begin()

  void Give( DATA * m_walk ) {
    m_walk->addr = m_clk ;
    m_clk++ ; // 賦予獨一無二位址
  } // Give()

  void Load() {

    m_clk = 0 ; // 重新開始計算
    string t ;
    string cmd[cmdNum] = { "cons", "list", "quote", "car", "cdr", "+", "-", "*", "/", "not", "and", "or",
                           ">", "<", ">=", "<=", "=", "string-append", "string>?", "string<?","string=?",
                           "eqv?", "equal?", "begin", "if", "cond", "atom?", "pair?", "list?", "null?",
                           "integer?", "real?", "number?", "string?", "boolean?", "symbol?", "define",
                           "clean-environment", "exit", "lambda", "let" } ;

    for ( int i = 0 ; i < cmdNum ; i++ ) {
      if ( m_function == NULL ) {
        m_temp = new DATA ;
        m_function = m_temp ;
        m_walk = m_function ;
      } // if
      else m_temp = new DATA ;

      NewNode( m_temp ) ;
      m_temp->inter = true ;
      m_temp->token = SYMBOL ;
      strcpy( m_temp->element, cmd[i].c_str() ) ;
      m_temp->next = new DATA ;
      NewNode( m_temp->next ) ;
      m_temp->next->inter = true ;
      t = "#<procedure " + cmd[i] + ">" ;
      strcpy( m_temp->next->element, t.c_str() ) ;
      Give( m_temp->next ) ;
      m_temp->next->token = SYMBOL ;
      m_temp->next->inter = true ;
      m_temp->next->mean = true ;
      m_walk->down = m_temp ;
      m_walk = m_walk->down ;
    } // for
  } // Load()

  void Proj_main() {
    m_current = NULL ;
    m_head = NULL ;
    m_walk = NULL ;
    m_temp = NULL ;
    m_error = NULL ;
    m_para = NULL ;
    m_tmpara = NULL ;
    m_line = 0 ;
    m_column = 0 ;
    m_left = 0 ;
    m_clk = 0 ;
    m_coda = 0 ;
    m_power = true ;
    m_function = NULL ;
    cout << "Welcome to OurScheme!\n" ;
    Load() ;
    do {
      ReadSExp() ;    // 讀取
    } while ( m_power ) ; // m_power控制工廠運作

    cout << endl << "Thanks for using OurScheme!" << endl ; // 感恩金主爸爸
  } // Proj_main()

  void ReadSExp() {  // ----------------------------------- 讀檔
    char temp[256] = { '\0' } ;
    char expr[256] ;  // 給Get_Token()的一排貨
    int g_call = -1 ;
    int err = -1 ;

    cin >> gTestNum ;
    cin.getline( expr, 256 ) ;   // 讀掉換行
    do {
      if ( cin.peek() == -1 ) { // end of file 回報錯誤並關閉電源
        err = 2 ;
        Print( err ) ;
        m_power = false ;
        return ;
      } // if

      cin.getline( expr, 256 ) ;
      g_call = -1 ;
      m_line++ ;
      m_column = 1 ;
      Get_token( expr, temp, 0, g_call ) ; // m_column == 0 Get_Token()負責更新標籤機的column數值
      if ( g_call == 1 ) m_power = false ;
      if ( g_call == 0 || g_call == 2 ) {
        m_line = 0 ;
      } // if
    } while ( m_power ) ;
  } // ReadSExp()

  void Get_token( char expr[256], char temp[256], int i, int & g_call ) {
    int err = -1 ;

    if ( temp[0] == '(' || temp[0] == ')' || temp[0] == '\'' || temp[0] == '\"' ) {
      Check( temp, g_call ) ;
      if ( g_call == 0 || g_call == 1 ) return ;
    } // if

    if ( i >= strlen( expr ) ) {
      Check( temp, g_call ) ;
      return ;
    } // if

    if ( expr[i] == '(' ) Check( temp, g_call ) ; // 把特殊符號也判斷一下
    else if ( expr[i] == ')' ) Check( temp, g_call ) ; // 把特殊符號也判斷一下
    else if ( expr[i] == '\"' ) { // 如果一開始為 '\"'
      Check( temp, g_call ) ;
      temp[0] = '\"' ;
      for ( i = i+1 ; i < strlen( expr ) && ( expr[i] != '\"' ||
                                              ( expr[i] == '\"' && expr[i-1] == '\\' ) ) ; i++ ) {
        temp[ strlen( temp ) ] = expr[ i ]  ;
      } // for

      if ( expr[i] != '\"' ) {
        err = 1 ;
        m_column = m_column+strlen( temp ) ;
        Print( err ) ;
        for ( int i = 0 ; i < 256 ; i++ )
          temp[i] = '\0' ;
        return ;
      } // if
    } // else if
    else if ( expr[i] == '\'' )  // QUOTE
      Check( temp, g_call ) ; // 把特殊符號也判斷一下

    else if ( expr[i] == ';' ) {
      Check( temp, g_call ) ;
      for ( ; i <= strlen( expr ) ; i++ )
        expr[i] = '\0' ;
      return ;
    } // else if
    else if ( expr[i] == ' ' ) {
      Check( temp, g_call ) ;
      m_column ++ ;    // 更新標籤機目前字元個數
    } // else if

    if ( g_call == 0 || g_call == 1 ) return ;
    if ( expr[i] != ' ' ) temp[ strlen( temp ) ] = expr[ i ] ;
    Get_token( expr, temp, i+1, g_call ) ;
  } // Get_token()

  void Check( char temp[256], int & g_call ) { // --------- 判斷種類在define
    int dot = 0 ;
    int num = 0 ;
    int err = -1 ;
    bool symbol = false ;
    bool havenum = false ;
    if ( g_call == 2 && m_line == 0 ) m_line++ ;
    if ( strcmp( temp, "" ) == 0 ) return ;
    else {
      m_temp = new DATA ;     // m_temp拿著新包裹
      NewNode( m_temp ) ;
    } // else

    if ( strcmp( temp, "(" ) == 0 ) m_temp->token = LEFT ;
    else if ( strcmp( temp, ")" ) == 0 ) m_temp->token = RIGHT ;
    else if ( strcmp( temp, "t" ) == 0 || strcmp( temp, "#t" ) == 0 ) m_temp->token = T ;
    else if ( strcmp( temp, "\'" ) == 0 || strcmp( temp, "quote" ) == 0 ) m_temp->token = QUOTE ;
    else if ( strcmp( temp, "." ) == 0 ) m_temp->token = DOT ;
    else if ( strcmp( temp, "()" ) == 0 || strcmp( temp, "nil" ) == 0 || strcmp( temp, "#f" ) == 0 )
      m_temp->token = NIL ;
    else if ( temp[0] == '\"' ) m_temp->token = STRING ;
    else {
      for ( int i = 0 ; i < strlen( temp ) && !symbol ; i++ ) {
        if ( temp[i] <= '9' && temp[i] >= '0' ) havenum = true ;
        else if ( ( temp[i] == '+' || temp[i] == '-' ) && i == 0 ) ;
        else if ( temp[i] == '.' ) dot++ ;
        else symbol = true ;
      } // for

      if ( dot > 1 || symbol || !havenum ) m_temp->token = SYMBOL ;
      else if ( dot == 1 && havenum ) m_temp->token = FLOAT ;
      else if ( dot == 0 && havenum ) m_temp->token = INT ;
      else m_temp->token = SYMBOL ;
    } // else

    strcpy( m_temp->element, temp ) ;
    m_temp->line = m_line ;
    m_temp->column = m_column ;

    if ( m_current == NULL ) m_current = m_temp ;
    else m_walk->next = m_temp ;

    for ( int i = 0 ; i < 256 ; i++ )
      temp[i] = '\0' ; // 清空籃子

    g_call = Grammer() ; // Grammer()工作 發出訊號給g_call對講機

    if ( g_call == 1 ) return ; // *********** (exit) ***********
    else if ( g_call == 2 || g_call == 0 ) {
      m_line = 1 ;
      m_column = 1 ;
    } // else if
    else if ( g_call == -1 )
      m_column = m_column + strlen( m_temp->element ) ;
  } // Check()

  int Grammer() {  // ------------------------------------- 檢查文法
    int err = -1 ;
    int i = 0 ;
    m_left = 0 ;
    DATA * qu = m_current ;
    while ( qu != NULL && strcmp( qu->element, "\'" ) == 0 ) {
      qu = qu->next ;
      if ( qu != NULL && strcmp( qu->element, "\'" ) != 0 ) i++ ;
    } // while

    if ( i == 0 && strcmp( m_current->element, "\'" ) == 0 ) {
      m_walk = m_temp ;
      return -1 ;  // 單純只有 '
    } // if
    else m_walk = m_current ;

    DATA * temp = NULL ;

    if ( m_walk->token == DOT || m_walk->token == RIGHT || strcmp( m_walk->element, "QUOTE" ) == 0 ) {
      err = 3 ;
      Print( err ) ;
      return 0 ;
    } // if

    for ( ; m_walk != NULL && temp == NULL ; m_walk = m_walk->next ) { // 開頭一定是對的
      if ( m_walk->token == QUOTE ) { // '
        if ( strcmp( m_walk->element, "quote" ) == 0 ) {
          if ( m_walk->next != NULL && ( m_walk->next->token == DOT || m_walk->next->token == QUOTE ) ) {
            err = 3 ; // *
            temp = m_walk ;
          } // if
        } // if
      } // if
      else if ( m_walk -> token == LEFT ) {
        m_left ++ ;
        if ( m_walk->next != NULL && m_walk->next->token == DOT ) {
          m_walk = m_walk -> next ;
          err = 3 ; // *****************************************
          temp = m_walk ;
        } // if
      } // else if
      else if ( m_walk->token == STRING || m_walk->token == INT || m_walk->token == FLOAT ||
                m_walk->token == NIL || m_walk->token == T || m_walk->token == SYMBOL ) { // atom
        if ( m_walk->next != NULL && strcmp( m_walk->next->element, "QUOTE" ) == 0 ) {
          err = 3 ;
          temp = m_walk ;
        } // if
      } // else if
      else if ( m_walk->token == DOT ) {
        if ( m_walk->next != NULL && ( m_walk->next->token == DOT || m_walk->next->token == RIGHT
                                       || strcmp( m_walk->next->element, "quote" ) == 0 ) ) { // 後面不能接...
          m_walk = m_walk -> next ;
          err = 3 ;
          temp = m_walk ;
        } // if
        else if ( m_walk->next != NULL ) {
          DATA * op = m_walk->next ;
          while ( op != NULL && strcmp( op->element, "\'" ) == 0 )
            op = op->next ;

          if ( op != NULL && op->token == LEFT ) {
            op = op->next ;
            int left = 1 ;
            for ( ; op != NULL && left != 0 ; op = op->next ) {
              if ( op->token == LEFT ) left++ ;
              if ( op->token == RIGHT ) left-- ;
            } // for

            if ( op != NULL && left == 0 && op->token != RIGHT ) { // 在有一個Sexp的情況下，op只能是 )
              m_walk = op ;
              err = 4 ;
              temp = m_walk ;
            } // if

          } // if
          else if ( op != NULL ) { // 後面接atom
            if ( op->next != NULL && op->next->token != RIGHT ) {
              m_walk = op->next ;
              err = 4 ;
              temp = m_walk ;
            } // if
          } // else if
        } // else if
      } // else if
      else if ( m_walk->token == RIGHT ) {
        m_left-- ;
        if ( m_walk->next != NULL && strcmp( m_walk->next->element, "QUOTE" ) == 0 ) {
          err = 3 ;
          temp = m_walk ;
        } // if
      } // else if
    } // for

    m_walk = m_temp ;

    if ( m_left > 0 && err == -1 ) return -1 ;
    else if ( m_left == 0 && err == -1 ) {
      Simplify() ;
      int end = 0 ;

      if ( m_current->next != NULL && m_current->next->next != NULL &&
           strcmp( m_current->element, "(" ) == 0 && strcmp( m_current->next->element, "exit" ) == 0 &&
           strcmp( m_current->next->next->element, ")" ) == 0 ) {
        err = 999 ;
        Print( err ) ;
        return 1 ;
      } // if
      else Semantics( err, end ) ;  // S-exp

      if ( end == 1 ) {
        m_head = NULL ;
        Print( err ) ;
        return 1 ;
      } // if

      return 2 ;
    } // else if
    else {             // err != -1
      m_walk = temp ;
      Print( err ) ;
      return 0 ;
    } // else
  } // Grammer()

  void Simplify() {  // ----------------------------------- 簡化該簡化的 ex: quote / () / .( 消除
    DATA * temp = m_walk ;
    m_walk = m_current ;
    if ( m_walk->next == NULL ) ;
    else {
      DATA * bef = NULL ;
      while ( m_walk != NULL ) {   // 第一次遍歷
        if ( strcmp( m_walk->element, "\'" ) == 0 ) {  // '
          DATA * n = new DATA ;
          NewNode( n ) ;
          n->token = LEFT ;
          strcpy( n->element, "(" ) ;
          n->next = new DATA ;
          NewNode( n->next ) ;
          n->next->token = QUOTE ;
          strcpy( n->next->element, "quote" ) ;

          if ( bef != NULL ) {
            bef = m_current ;
            while ( strcmp( bef->next->element, "\'" ) != 0 ) {
              bef = bef->next ;
            } // while

            n->next->next = bef->next->next ;
            bef->next = n ;  // 處理 ' 不在第一個的情況
          } // if
          else {
            n->next->next = m_current->next ;
            m_current = n ;                // ' 為第一個
            bef = m_current ;
          } // else

          n = new DATA ;
          NewNode( n ) ;
          n->token = RIGHT ;
          strcpy( n->element, ")" ) ;

          DATA * m = m_walk ;
          while ( strcmp( m->next->element, "\'" ) == 0 ) m = m->next ;

          if ( m->next->token == LEFT ) {  // ' 後面接 (expr)
            for ( int i = 0 ; m->next != NULL && n != NULL ; m = m->next ) {
              if ( m->next->token == LEFT ) i++ ;
              else if ( m->next->token == RIGHT ) i-- ;

              if ( i == 0 ) {
                n->next = m->next->next ;
                m->next->next = n ;
                n = NULL ;
              } // if
            } // for
          } // if
          else {   // ' 後面接atom
            n->next = m->next->next ;
            m->next->next = n ;
          } // else
        } // if

        if ( m_walk->token == INT || m_walk->token == FLOAT ) DoNum( m_walk ) ;
        m_walk = m_walk->next ;
        bef = m_current ;
      } // while

      m_walk = m_current ;
      while ( m_walk != NULL ) {   // 第二次遍歷
        if ( m_walk->token == LEFT && m_walk->next->token == RIGHT ) {  // 將()轉為NIL
          strcpy( m_walk->element, "nil" ) ;
          m_walk->token = NIL ;
          m_walk->next = m_walk->next->next ;
        } // if
        else if ( m_walk->next != NULL && m_walk->next->next != NULL &&
                  m_walk->next->token == DOT && m_walk->next->next->token == LEFT ) { // 消掉 .(
          m_walk->next = m_walk->next->next->next ;

          int count = 0 ;
          bool out = false ;
          DATA * tmp = m_walk ;
          for ( ; tmp->next != NULL && !out ; tmp = tmp->next ) {
            if ( tmp->next->token == LEFT ) count++ ;
            else if ( tmp->next->token == RIGHT && count != 0 ) count-- ;
            else if ( tmp->next->token == RIGHT && count == 0 ) {  // 消掉對應的右括號
              tmp->next = tmp->next->next ;
              out = true ;
            } // else if
          } // for

        } // else if
        else if ( m_walk->next != NULL && m_walk->next->next != NULL &&      // 消掉 .()
                  m_walk->next->token == DOT && m_walk->next->next->token == NIL ) {
          m_walk->next = m_walk->next->next->next ;
        } // else if

        if (  strcmp( m_walk->element, "nil" ) == 0 ) {
          if ( m_walk->next != NULL && m_walk->next->next != NULL &&
               m_walk->next->token == DOT && ( m_walk->next->next->token == LEFT ||
                                               m_walk->next->next->token == NIL ) ) ;
          else m_walk = m_walk->next ;
        } // if
        else m_walk = m_walk->next ;

        bef = m_current ;
      } // while

    } // else

    /*
    cout << endl << endl ;
    cout << "---------------------------" << endl << endl ;
    for ( m_walk = m_current ; m_walk != NULL ; m_walk = m_walk->next ) {
      cout << m_walk->element << " " ;
    }
    cout << endl << endl ;
    */
    m_walk = temp ;
  } // Simplify()

  void DoDoubleQuote( DATA * tmp ) {  // ------------------ 處理雙引號 (需要m_walk指向STRING)
    char temp[10] = { '\0' } ;
    DATA * tempPtr = NULL ;
    DATA * stop = tmp ;

    for ( int index = 0 ; index < strlen( tmp -> element ) ; index++ ) {
      if ( tmp->element[index] == '\\' ) { // 特殊符號

        if ( tmp->element[index+1] == '\\' || tmp->element[index+1] == '\"' ) {  // \' or \"
          for ( int i = index ; i < strlen( tmp->element ) ; i++ ) // 往前一格
            tmp->element[i] = tmp->element[i+1] ;

        } // if
        else if ( tmp->element[index+1] == 't' ) { // \t
          index++ ;
          int k = index+1 ;
          int original = strlen( tmp->element ) ;
          for (  ; k < original ; k++ )  // 先往後4格
            tmp->element[k+2] =  tmp->element[k] ;

          tmp->element[k+2] = '\0' ;

          for ( int j = index-1 ; j < index+3 ; j++ )
            tmp->element[j] =  ' ' ;
        } // else if
        else if ( tmp->element[index+1] == 'n' ) {  // \n
          tempPtr = new DATA ;

          tempPtr->next = tmp->next ;
          tmp->next = tempPtr ;
          tempPtr->token = STRINGs ;
          tempPtr->line = tmp->line ;
          tempPtr->column = tmp->column + index + 1 ; // 這條column跳2格因為去掉 \n

          int i = index + 2 ;
          for ( i = index+2 ; i < strlen( tmp->element ) ; i++ )
            tempPtr->element[ i-index-2 ] = tmp->element[i] ;

          tempPtr->element[ i-index-2 ] = '\0' ; // 關起來

          for ( i = index ; i < strlen( tmp->element ) ; i++ )
            tmp->element[i] = '\0' ;

          index = -1 ;
          tmp = tmp->next ;
        } // else if
      } // if
    } // for

    tmp = stop ;
  } // DoDoubleQuote()

  void DoNum( DATA * tmp ) {  // -------------------------- 處理數字 (需要m_walk指向數字)
    for ( int i = 0 ; i < strlen( tmp->element ) ; i++ ) {
      if ( tmp->element[i] == '+' ) {    // 遇到 + 則忽略，全部往前移一格
        int j = i ;
        for ( ; j+1 < strlen( tmp->element ) ; j++  )
          tmp->element[j] = tmp->element[j+1] ;

        tmp->element[j] = '\0' ;
      } // if

      if ( tmp->element[i] == '.' ) {
        if ( i == 0 || ( i == 1 && tmp->element[0] == '-' ) ) { // . / -.
          if ( i == 0 ) {
            for ( int j = strlen( tmp->element ) - 1 ; j >= 0 ; j--  )
              tmp->element[j+1] = tmp->element[j] ;

            tmp->element[0] = '0' ;
          } // if
          else {
            for ( int j = strlen( tmp->element ) - 1 ; j > 0 ; j--  )
              tmp->element[j+1] = tmp->element[j] ;

            tmp->element[1] = '0' ;
          } // else

          i++ ;
        } // if

        string s1 = string( tmp->element ) ;
        stringstream s2 ;

        s2 << setprecision( 3 ) << fixed << atof( s1.c_str() ) ;
        s2 >> s1 ;
        strcpy( tmp->element, s1.c_str() ) ;
      } // if
    } // for
  } // DoNum()

  void NewNode( DATA * node ) {  // ----------------------- 初始化新的node
    node->inter = false ;
    node->mean = false ;
    node->finish = false ;
    node->token = 0 ;    // atom S-exp類型(貨物類型)
    node->line = 0 ;     // 行標籤
    node->column = 0 ;   // 列標籤
    Give( node ) ;
    node->next = NULL ;
    node->down = NULL ;
    for ( int i = 0 ; i < 256 ; i++ )
      node->element[i] = '\0' ;

  } // NewNode()

  void Copy( DATA * temp, DATA * current, const char special[256] ) {  // 複製struct
    temp->token = current->token ;    // atom S-exp類型(貨物類型)
    temp->line = current->line ;      // 行標籤
    temp->column = current->column ;  // 列標籤
    temp->finish = current->finish ;
    temp->next = NULL ;
    temp->down = NULL ;
    temp->inter = current->inter ;
    temp->mean = current->mean ;
    strcpy( temp->element, special ) ;
    temp->addr = current->addr ;
  } // Copy()

  void BuildDS( DATA * temp, int & left, bool & back ) {  // 建立結構
    if ( m_current == NULL ) return ;

    else if ( strcmp( m_current->element, "(" ) == 0 ) {   // ============ 為左括號 ===========
      Copy( temp, m_current, "(" ) ;
      temp->down = new DATA ;
      NewNode( temp->down ) ;
      m_current = m_current->next ;
      left++ ;
      BuildDS( temp->down, left, back ) ;  // 往下一層
    } // else if

    else if ( strcmp( m_current->element, ")" ) == 0 ) {   // ============ 為右括號 ============
      left-- ;
      Copy( temp, m_current, ")" ) ;
      back = true ;
      return ;    // 返回上一層
    } // else if

    else if ( strcmp( m_current->element, "." ) == 0 ) {    // =========== 為 . ===============
      Copy( temp, m_current, "." ) ;
      temp->next = new DATA ;
      NewNode( temp->next ) ;
      m_current = m_current->next ;
      if ( m_current == NULL ) return ;
      BuildDS( temp->next, left, back ) ;
    } // else if

    else {                                                 // ============== 為元素 =============
      Copy( temp, m_current, m_current->element ) ;
      m_current = m_current->next ;
      if ( m_current == NULL ) return ;
      else {
        temp->next = new DATA ;
        NewNode( temp->next ) ;
        BuildDS( temp->next, left, back ) ;
      } // else
    } // else

    if ( back && strcmp( temp->element, "(" ) != 0 )
      return ;  // 回到上一次下來的地方
    else if ( back && strcmp( temp->element, "(" ) == 0 ) {
      back = false ;

      m_current = m_current->next ;
      if ( left == 0 ) return ;
      else if ( m_current != NULL ) {  // 後面還有東西
        temp->next = new DATA ;
        NewNode( temp->next ) ;
        BuildDS( temp->next, left, back ) ;
      } // else if
    } // else if
  } // BuildDS()

  void Print( int & err ) {
    cout << endl << "> " ;
    if ( err != -1 ) Error( err ) ;
    else {   // <S-exp>
      m_walk = m_head ;
      int count = 0 ;
      bool downLeft = true ;
      PrintDS( m_walk, count, downLeft ) ;
    } // else

    m_head = NULL ;
    m_current = NULL ;
    m_error = NULL ;
    m_line = 0 ;
    m_column = 0 ;
    m_left = 0 ;
    m_coda = 0 ;
    return ;
  } // Print()

  void PrintDS( DATA * m_walk, int & count, bool & downLeft ) {  // 根據結構印出來 ( 遞迴 )
    for (  ; m_walk != NULL ; m_walk = m_walk->next ) {
      if ( m_walk->down != NULL ) {

        if ( !downLeft )  // 判斷要印幾個' ' 才符合格式
          for ( int i = 0 ; i < count ; i++ )
            cout << "  " ;

        cout << "( " ;
        count++ ;
        downLeft = true ;
        PrintDS( m_walk->down, count, downLeft ) ;
      } // if

      if ( m_walk->token == STRING || m_walk->token == INT || m_walk->token == QUOTE ||
           m_walk->token == DOT || m_walk->token == NIL || m_walk->token == FLOAT ||
           m_walk->token == SYMBOL || m_walk->token == T ) {

        if ( !downLeft )  // 判斷要印幾個' ' 才符合格式
          for ( int i = 0 ; i < count ; i++ )
            cout << "  " ;

        if ( m_walk->token == STRING ) {
          DoDoubleQuote( m_walk ) ;
          cout << m_walk->element << endl ;
          while ( m_walk->next != NULL && m_walk->next->token == STRINGs ) {
            m_walk = m_walk->next ;
            cout << m_walk->element << endl ;
          } // while
        } // if
        else if ( m_walk->token == NIL ) cout << "nil\n" ;
        else if ( m_walk->token == T ) cout << "#t\n" ;
        else {

          if ( m_walk->token == INT || m_walk->token == FLOAT ) DoNum( m_walk ) ;
          cout << m_walk->element << endl ;
        } // else
      } // if

      else if ( strcmp( m_walk->element, ")" ) == 0 ) {
        count-- ;

        if ( !downLeft )
          for ( int i = 0 ; i < count ; i++ )
            cout << "  " ;

        cout << m_walk->element << endl ;
      } // else if

      downLeft = false ;
    } // for
  } // PrintDS()

  void Error( int & e ) {  // ----------------------------- 處理error輸出問題
    int count = 0 ;
    bool downLeft = true ;
    if ( m_error != NULL && m_error->token == LEFT ) {
      if ( m_error->down != NULL && m_error->down->token == RIGHT ) {
        strcpy( m_error->element, "nil" ) ;
        m_error->token = NIL ;
        m_error->down = NULL ;
      } // if
    } // if

    if ( e == 1 )
      cout << "ERROR (no closing quote) : END-OF-LINE encountered at Line "
           << m_line << " Column " << m_column << endl ;
    else if ( e == 2 )
      cout << "ERROR (no more input) : END-OF-FILE encountered" ;
    else if ( e == 3 )
      cout << "ERROR (unexpected token) : atom or '(' expected when token at Line "
           << m_walk->line << " Column " << m_walk->column << " is >>" << m_walk->element << "<<\n" ;
    else if ( e == 4 )
      cout << "ERROR (unexpected token) : ')' expected when token at Line "
           << m_walk->line << " Column " << m_walk->column << " is >>" << m_walk->element << "<<\n" ;
    else if ( e == 5 )
      cout << "ERROR (unbound symbol) : " << m_error->element << endl ;
    else if ( e == 6 ) {
      cout << "ERROR (non-list) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 7 ) {
      cout << "ERROR (attempt to apply non-function) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 8 )
      cout << "ERROR (level of CLEAN-ENVIRONMENT)" << endl ;
    else if ( e == 9 )
      cout << "ERROR (level of DEFINE)" << endl ;
    else if ( e == 10 )
      cout << "ERROR (level of EXIT)" << endl ;
    else if ( e == 11 ) {
      cout << "ERROR (DEFINE format) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 12 ) {
      cout << "ERROR (SET! format) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 13 ) {
      cout << "ERROR (LAMBDA format) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 14 ) {
      cout << "ERROR (LET format) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 15 ) {
      cout << "ERROR (COND format) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 16 )
      cout << "ERROR (incorrect number of arguments) : " << m_error->element << endl ;
    else if ( e == 17 ) {
      cout << "ERROR (" << m_temp->element << " with incorrect argument type) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 18 ) {
      cout << "ERROR (no return value) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 19 )
      cout << "ERROR (division by zero) : /" << endl ;
    else if ( e == 20 ) {
      cout << "ERROR (unbound parameter) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 21 ) {
      cout << "ERROR (unbound test-condition) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if
    else if ( e == 22 ) {
      cout << "ERROR (unbound condition) : " ;
      PrintDS( m_error, count, downLeft ) ;
    } // else if

    m_walk = NULL ; // 只要進到錯誤 m_walk指著的東西都要丟掉
    m_current = NULL ;
    e = -1 ;
    return ;
  } // Error()
} ; // end of class PROJ1

int main() {
  PL proj ;
  proj.Proj_main() ;
} // main()
