#lang racket/gui

(require math/array
         future-visualizer)

(define possibilities (set 1 2 3 4 5 6 7 8 9))

(define-struct (exn:fail:sudoku exn:fail) ())
(define (sudoku-error msg . v)
  (raise
   (make-exn:fail:sudoku msg (current-continuation-marks))))

; sudoku grids are arrays of lists, where each
; list contains the remaining possible values for
; that array location
(define (make-sudoku-grid)
  (array->mutable-array (make-array #(9 9) possibilities)))

(define (update-grid grid _row _col val)
  (define new (mutable-array-copy grid))

  (let ([row (sub1 _row)]
        [col (sub1 _col)])
    ; make our change
    (if (set-member? (array-ref new (vector row col)) val)
        (array-set! new (vector row col) (set val))
        (sudoku-error "can't set cell to eliminated value"))
        
    ; now we need to make the new grid consistent
    (let loop ([affected (list (vector row col))]
               [new-affected '()])
      (for ([v (in-list affected)])
        (match-let ([(vector row col) v])
          (when (set-empty? (array-ref new v))
            (sudoku-error "cell empty at" (add1 row) (add1 col)))
          
          (define verboten (set-first (array-ref new v)))

          ; horizontal
          (for ([r (in-range 0 9)]
                #:when (not (= row r)))
            (let* ([v (vector r col)]
                   [orig (array-ref new v)])
              (when (set-member? orig verboten)
                (define new-value (set-remove orig verboten))
                (define new-val-count (set-count new-value))
                (cond
                  [(= 1 new-val-count)
                   (set! new-affected (cons v new-affected))]
                  [(= 0 new-val-count)
                   (sudoku-error "emptied out a cell unexpectedly!")])
                (array-set! new v new-value)
                )))

          ; vertical
          (for ([c (in-range 0 9)]
                #:when (not (= col c)))
            (let* ([v (vector row c)]
                   [orig (array-ref new v)])
              (when (set-member? orig verboten)
                (define new-value (set-remove orig verboten))
                (define new-val-count (set-count new-value))
                (cond
                  [(= 1 new-val-count)
                   (set! new-affected (cons v new-affected))]
                  [(= 0 new-val-count)
                   (sudoku-error "emptied out a cell unexpectedly!")])
                (array-set! new v new-value)
                )))

          ; square
          (let ([sq-row (* (quotient row 3) 3)]
                [sq-col (* (quotient col 3) 3)])
            (for* ([r (in-range sq-row (+ sq-row 3))]
                   [c (in-range sq-col (+ sq-col 3))]
                   #:when (not (and (= row r) (= col c))))
              (let* ([v (vector r c)]
                     [orig (array-ref new v)])
                (when (set-member? orig verboten)
                  (define new-value (set-remove orig verboten))
                  (define new-val-count (set-count new-value))
                  (cond
                    [(= 1 new-val-count)
                     (set! new-affected (cons v new-affected))]
                    [(= 0 new-val-count)
                     (sudoku-error "emptied out a cell unexpectedly!")])
                  (array-set! new v new-value)
                  ))))

          (when (not (empty? new-affected))
            (loop new-affected '()))
          ))))
  new)
    
(define (render-grid grid)
  (for ([row (in-range 0 9)])
    (printf "+----+----+----+----+----+----+----+----+----+~n")
    (printf "|")
    (for ([col (in-range 0 9)])
      (let ([v (sort (set->list (array-ref grid (vector row col))) <)])
        (cond
          [(= (length v) 1)
           (printf " ~a  " (car v))]
          [(= (length v) 2)
           (printf "~a ~a " (car v) (cadr v))]
          [(= (length v) 3)
           (printf "~a~a~a " (car v) (cadr v) (caddr v))]
          [(= (length v) 4)
           (printf "~a~a~a~a" (car v) (cadr v) (caddr v) (cadddr v))]
          [else
           (printf " ?~a?" (length v))])
        (printf "|")))
    (printf "~n"))
    (printf "+----+----+----+----+----+----+----+----+----+~n"))  

(define (multi-update-grid grid values)
  (for/fold ([g grid])
    ([v (in-list values)])
    (apply update-grid (cons g v))))

(define g (time (multi-update-grid
           (make-sudoku-grid)
           '(
             (2 1 1)
             (2 7 3)
             (2 9 2)
             (3 2 6)
             (3 5 3)
             (3 6 9)
             (3 8 4)
             (3 9 7)
             (4 4 2)
             (4 5 7)
             (4 7 1)
             (5 2 8)
             (5 4 4)
             (5 8 7)
             (6 3 3)
             (6 5 5)
             (6 6 1)
             (6 7 6)
             (7 1 6)
             (7 2 2)
             (7 5 8)
             (7 8 9)
             (8 1 5)
             (8 3 8)
             (8 9 3)
             ))))

(define (find-minimum-choices grid)
  (define per-cell-remaining
    (for*/list ([row (in-range 0 9)]
                [col (in-range 0 9)])
      (list (set-count (array-ref grid (vector row col)))
            row col)))

  (define choice-remaining
    (filter (lambda (v) (> (car v) 1))
            per-cell-remaining))
  
  (define sorted-choices
    (sort choice-remaining
          (lambda (a b) (< (car a) (car b)))))
  
  (if (> (length sorted-choices) 1)
      (map add1 (cdar sorted-choices))
      #f))

(define (split-on-cell grid row col)
  (define values (array-ref grid (vector (sub1 row) (sub1 col))))
  (when (= (set-count values) 1)
    (sudoku-error "tried to split singleton"))
  (for/fold ([l '()])
    ([v (in-set values)])
    (with-handlers ([exn:fail:sudoku? (λ (e) l)])
      (cons
       (update-grid grid row col v)
       l))))

(define (solvable? grid)
  (let/ec done
    (for ([v (in-array grid)])
      (when (<= (set-count v) 0)
        (done #f)))
    #t))

(define (solved? grid)
  (let/ec done
    (for ([v (in-array grid)])
      (when (not (= (set-count v) 1))
        (done #f)))
    #t))

(solved? g)

(define (solve grid #:depth [depth 0])
  ;(printf "~a~n" depth)
  (let/ec solution
    (when (solved? grid)
      (solution grid))
    (define split-cell (find-minimum-choices grid))
    (when (not split-cell)
      (sudoku-error "no solved, but no decision to make?"))
    (define possibilities (apply split-on-cell (cons grid split-cell)))
    (for/list ([p possibilities])
      (when (solvable? p)
        (with-handlers ([exn:fail:sudoku? (λ (e) #f)])
          (solution (solve p #:depth (add1 depth))))))
    (sudoku-error "nothing worked")
    ))

;(render-grid g)
;(render-grid
; (time (solve g)))

(define f (new frame% [label "Sudoku"] [width 384] [height 384]))

(send f show #t)

(define sudoku-canvas%
  (class* canvas% ()
    (init-field grid highlights show-tiny?
                selection-callback undo-callback
                solve-callback)
    
    (define/override (on-char e)
      (when (equal? (send e get-key-code) #\backspace)
        (undo-callback this))
      (when (equal? (send e get-key-code) #\s)
        (solve-callback this)))
    
    (define/override (on-event e)
      (when (send e button-down? 'left)
        (define dc (send this get-dc))
        (define-values (_w _h) (send dc get-size))      
        (define w (* 19/20 (min _w _h)))
        (define h (* 19/20 (min _w _h)))
        (define x (+ (* 1/40 _w) (max 0 (/ (- (* 19/20 _w) w) 2))))
        (define y (+ (* 1/40 _h) (max 0 (/ (- (* 19/20 _h) h) 2))))
        
        (define grid-x (/ (- (send e get-x) x) w))
        (define grid-y (/ (- (send e get-y) y) h))
        
        (define rough-row (floor (* 9 grid-y)))
        (define rough-col (floor (* 9 grid-x)))
        (define fine-row (floor (* 3 (/ (- grid-y (/ rough-row 9)) 1/9))))
        (define fine-col (floor (* 3 (/ (- grid-x (/ rough-col 9)) 1/9))))
        (define exact-number (+ 1 fine-col (* fine-row 3)))

        (define cell-contents (array-ref grid (vector rough-row rough-col)))
        
        (when (and (> (set-count cell-contents) 1)
                   (set-member? cell-contents exact-number))
          (selection-callback this
                              (add1 rough-row)
                              (add1 rough-col)
                              exact-number))
      ))
    
    (define/override (on-paint)
      (define dc (send this get-dc))
      (define-values (_w _h) (send dc get-size))
      (send dc draw-rectangle 0 0 _w _h)
      
      (define w (* 19/20 (min _w _h)))
      (define h (* 19/20 (min _w _h)))
      (define x (+ (* 1/40 _w) (max 0 (/ (- (* 19/20 _w) w) 2))))
      (define y (+ (* 1/40 _h) (max 0 (/ (- (* 19/20 _h) h) 2))))
      
      (define thin (make-object pen% (make-object color% 0 0 0 0.333) 1 'solid))
      (define thick (make-object pen% "black" 2 'solid))
      
      (for ([x-frac (in-range 0 10/9 1/9)])
        (if (= (denominator x-frac) 9)
            (send dc set-pen thin)
            (send dc set-pen thick))
        (send dc draw-line
              (+ x (* w x-frac))
              y
              (+ x (* w x-frac))
              (+ y h)))
      (for ([y-frac (in-range 0 10/9 1/9)])
        (if (= (denominator y-frac) 9)
            (send dc set-pen thin)
            (send dc set-pen thick))
        (send dc draw-line
              x
              (+ y (* w y-frac))
              (+ x w)
              (+ y (* w y-frac))))
      
      (define single-digit-font
        (make-object font% (inexact->exact (round (/ h 10)))
          'default 'normal 'normal #f 'default #t))
      (define nine-digit-font
        (make-object font% (inexact->exact (round (/ h 30)))
          'default 'normal 'normal #f 'default #t))
      (send dc set-font nine-digit-font)
      (define-values (9tw _a _b _c) (send dc get-text-extent "5"))
      
      (for* ([row (in-range 0 9)]
             [col (in-range 0 9)])
        (let ([contents (array-ref grid (vector row col))])
          (when (= 1 (set-count contents))
            (send dc set-font single-digit-font)
            (define s (number->string (set-first contents)))
            (define-values (tw th td tv) (send dc get-text-extent s))
            (send dc draw-text s
                  (+ x (* col (/ w 9)) (- (/ w 18) (/ tw 2)))
                  (+ y (* row (/ h 9)))))
          (when (and (> (set-count contents) 1) show-tiny?)
            (for ([v contents])
              (send dc set-font nine-digit-font)
              (if (member (list row col v) highlights)
                  (send dc set-text-foreground "red")
                  (send dc set-text-foreground "black"))
              (send dc draw-text (number->string v)
                    (+ x (* col (/ w 9))
                       (* (remainder (sub1 v) 3) (/ w 27))
                       (- (/ w 54) (/ 9tw 2)))
                    (+ y (* row (/ h 9))
                       (* (quotient (sub1 v) 3) (/ h 27))))
              )
            (send dc set-text-foreground "black")))))
    
    (define/public (replace-grid new-grid [new-highlights '()])
      (set! grid new-grid)
      (set! highlights new-highlights))

    (define/public (add-highlight row col num)
      (set! highlights (cons (list (sub1 row) (sub1 col) num) highlights))) 
    (define/public (replace-highlights newh)
      (set! highlights newh))
    (define/public (get-highlights)
      highlights)
    (define/public (get-grid)
      grid)

    (super-new)))

(define grid-history '())

(define (selection-callback canvas row col value)
  (with-handlers
      ([exn:fail:sudoku?
        (lambda (e)
          (send canvas add-highlight row col value)
          (send canvas on-paint))])
    (let ([orig-grid (send canvas get-grid)]
          [orig-highlights (send canvas get-highlights)])
      (send canvas replace-grid
            (update-grid orig-grid row col value))
      (set! grid-history (cons (cons orig-grid orig-highlights) grid-history))
      (send canvas on-paint))))

(define c
  (new sudoku-canvas%
       [parent f]
       [grid g]
       [highlights '()]
       [show-tiny? #t]
       [selection-callback selection-callback]
       [undo-callback
        (lambda (canvas)
          (when (> (length grid-history) 0)
            (match-let
                ([(list-rest (list-rest grid highlights) leftovers) grid-history])
              (set! grid-history leftovers)
              (send canvas replace-grid grid highlights)
              (send canvas on-paint))))]
       [solve-callback
        (lambda (canvas)
          (thread
           (lambda ()
             (let ([orig-grid (send canvas get-grid)]
                   [orig-highlights (send canvas get-highlights)])
               (send canvas replace-grid (solve orig-grid))
               (send canvas on-paint)
               (set! grid-history (cons (cons orig-grid orig-highlights) grid-history))))))]
       ))

(send c replace-grid g)