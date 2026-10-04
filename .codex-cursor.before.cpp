#include "drawingtestwidget.h"
#include "projectedbrush.h"
#include "brushperformance.h"
#include "localization.h"

#include <QHBoxLayout>
#include <QLabel>
#include <QKeyEvent>
#include <QMouseEvent>
#include <QPainter>
#include <QPainterPath>
#include <QPainterPathStroker>
#include <QPaintEvent>
#include <QPushButton>
#include <QRadialGradient>
#include <QEnterEvent>
#include <QElapsedTimer>
#include <QFocusEvent>
#include <QApplication>
#include <QBitmap>
#include <QDebug>
#include <QMenu>
#include <QPolygonF>
#include <QRandomGenerator>
#include <QTabletEvent>
#include <QTextDocument>
#include <QVBoxLayout>
#include <QtConcurrentRun>
#include <QStringList>

#include <cmath>
#include <cstring>
#include <limits>

namespace {
quint64 mixStrokeRandom(quint64 value)
{
    value += 0x9e3779b97f4a7c15ULL;
    value = (value ^ (value >> 30)) * 0xbf58476d1ce4e5b9ULL;
    value = (value ^ (value >> 27)) * 0x94d049bb133111ebULL;
    return value ^ (value >> 31);
}

qreal strokeRandom01(quint64 seed, quint64 dab, quint64 symmetry, quint64 particle, quint64 channel)
{
    quint64 value = mixStrokeRandom(seed ^ 0xd1b54a32d192ed03ULL);
    value = mixStrokeRandom(value ^ dab);
    value = mixStrokeRandom(value ^ (symmetry * 0x9e3779b97f4a7c15ULL));
    value = mixStrokeRandom(value ^ (particle * 0xbf58476d1ce4e5b9ULL));
    value = mixStrokeRandom(value ^ (channel * 0x94d049bb133111ebULL));
    // Use the high 53 bits so every returned value is exactly representable by
    // double and stays in [0, 1), independent of platform RNG implementations.
    return qreal(value >> 11) * (1.0 / 9007199254740992.0);
}
} // namespace

namespace {
QRegion paddedUvFillRegion(const QPainterPath &path, const QSize &size)
{
    QBitmap coverage(size);
    coverage.fill(Qt::color0);
    QPainter painter(&coverage);
    painter.setRenderHint(QPainter::Antialiasing, false);
    painter.setPen(QPen(Qt::color1, 2.0, Qt::SolidLine, Qt::RoundCap, Qt::RoundJoin));
    painter.setBrush(Qt::color1);
    painter.drawPath(path);
    painter.end();
    return QRegion(coverage);
}

QString L(const char *key, const char *fallback)
{
    return Localization::instance().text(QString::fromUtf8(key), QString::fromUtf8(fallback));
}

bool isGroupLayerType(const QString &type)
{
    return type.trimmed().compare(QStringLiteral("group"), Qt::CaseInsensitive) == 0;
}

bool isFillLayerType(const QString &type)
{
    return type.trimmed().compare(QStringLiteral("fill"), Qt::CaseInsensitive) == 0;
}

QImage grayscaleImagePreservingAlpha(const QImage &image)
{
    if (image.isNull()) {
        return QImage();
    }
    const QImage source = image.convertToFormat(QImage::Format_ARGB32);
    QImage result(source.size(), QImage::Format_ARGB32);
    for (int y = 0; y < source.height(); ++y) {
        const QRgb *src = reinterpret_cast<const QRgb *>(source.constScanLine(y));
        QRgb *dst = reinterpret_cast<QRgb *>(result.scanLine(y));
        for (int x = 0; x < source.width(); ++x) {
            const int gray = qGray(src[x]);
            dst[x] = qRgba(gray, gray, gray, qAlpha(src[x]));
        }
    }
    return result.convertToFormat(QImage::Format_ARGB32_Premultiplied);
}

bool isDescendantLayerOf(const QVector<DrawingCanvas::RasterLayer> &layers, int layerIndex, int ancestorIndex)
{
    if (layerIndex < 0 || layerIndex >= layers.size() || ancestorIndex < 0 || ancestorIndex >= layers.size()) {
        return false;
    }

    int guard = 0;
    int cursor = layers.at(layerIndex).parentIndex;
    while (cursor >= 0 && cursor < layers.size() && guard < layers.size()) {
        if (cursor == ancestorIndex) {
            return true;
        }
        cursor = layers.at(cursor).parentIndex;
        ++guard;
    }
    return false;
}

QPainter::CompositionMode compositionModeForBlend(const QString &blendMode)
{
    const QString mode = blendMode.trimmed().toLower();
    if (mode == QStringLiteral("multiply")) {
        return QPainter::CompositionMode_Multiply;
    }
    if (mode == QStringLiteral("screen")) {
        return QPainter::CompositionMode_Screen;
    }
    if (mode == QStringLiteral("overlay")) {
        return QPainter::CompositionMode_Overlay;
    }
    if (mode == QStringLiteral("darken")) {
        return QPainter::CompositionMode_Darken;
    }
    if (mode == QStringLiteral("lighten")) {
        return QPainter::CompositionMode_Lighten;
    }
    if (mode == QStringLiteral("plus") || mode == QStringLiteral("add")) {
        return QPainter::CompositionMode_Plus;
    }
    return QPainter::CompositionMode_SourceOver;
}

QPointF rotatePointAround(const QPointF &point, const QPointF &center, qreal degrees)
{
    if (std::abs(degrees) < 0.0001) {
        return point;
    }

    const qreal radians = degrees * 3.14159265358979323846 / 180.0;
    const qreal s = std::sin(radians);
    const qreal c = std::cos(radians);
    const QPointF delta = point - center;
    return QPointF(center.x() + delta.x() * c - delta.y() * s,
                   center.y() + delta.x() * s + delta.y() * c);
}

qreal dot2(const QPointF &a, const QPointF &b)
{
    return a.x() * b.x() + a.y() * b.y();
}

qreal normalizeDegrees(qreal degrees)
{
    qreal d = std::fmod(degrees, 360.0);
    if (d > 180.0) {
        d -= 360.0;
    } else if (d < -180.0) {
        d += 360.0;
    }
    return d;
}

qreal clampScaleSigned(qreal value)
{
    const qreal sign = (value < 0.0) ? -1.0 : 1.0;
    return sign * qMax<qreal>(0.02, std::abs(value));
}

QCursor makeSelectionBadgeCursor(bool subtract)
{
    QPixmap pixmap(24, 24);
    pixmap.fill(Qt::transparent);

    QPainter p(&pixmap);
    p.setRenderHint(QPainter::Antialiasing, true);
    p.setPen(QPen(QColor(20, 20, 20, 240), 2.0));
    p.drawLine(QPointF(4.0, 12.0), QPointF(12.0, 12.0));
    p.drawLine(QPointF(8.0, 8.0), QPointF(8.0, 16.0));
    p.setPen(QPen(QColor(245, 245, 245, 245), 1.0));
    p.drawLine(QPointF(4.0, 12.0), QPointF(12.0, 12.0));
    p.drawLine(QPointF(8.0, 8.0), QPointF(8.0, 16.0));

    const QRectF badgeRect(13.0, 13.0, 9.0, 9.0);
    p.setBrush(QColor(255, 255, 255, 240));
    p.setPen(QPen(QColor(12, 12, 12, 245), 1.2));
    p.drawEllipse(badgeRect);
    p.setPen(QPen(subtract ? QColor(205, 50, 50, 255) : QColor(35, 150, 60, 255), 1.6));
    p.drawLine(QPointF(15.6, 17.5), QPointF(19.4, 17.5));
    if (!subtract) {
        p.drawLine(QPointF(17.5, 15.6), QPointF(17.5, 19.4));
    }
    p.end();

    return QCursor(pixmap, 8, 12);
}

QCursor makeFreeTransformRotateCursor()
{
    QPixmap pixmap(24, 24);
    pixmap.fill(Qt::transparent);

    QPainter p(&pixmap);
    p.setRenderHint(QPainter::Antialiasing, true);

    const QRectF arcRect(4.5, 4.5, 15.0, 15.0);
    p.setPen(QPen(QColor(20, 20, 20, 240), 2.4, Qt::SolidLine, Qt::RoundCap, Qt::RoundJoin));
    p.drawArc(arcRect, 35 * 16, 250 * 16);
    p.setPen(QPen(QColor(250, 250, 250, 245), 1.2, Qt::SolidLine, Qt::RoundCap, Qt::RoundJoin));
    p.drawArc(arcRect, 35 * 16, 250 * 16);

    QPolygonF arrow;
    arrow << QPointF(17.6, 4.4) << QPointF(21.6, 5.8) << QPointF(18.8, 8.9);
    p.setBrush(QColor(255, 255, 255, 245));
    p.setPen(QPen(QColor(18, 18, 18, 235), 1.0));
    p.drawPolygon(arrow);
    p.end();

    return QCursor(pixmap, 12, 12);
}

const QCursor &selectionAddCursor()
{
    static QCursor cursor = makeSelectionBadgeCursor(false);
    return cursor;
}

const QCursor &selectionSubtractCursor()
{
    static QCursor cursor = makeSelectionBadgeCursor(true);
    return cursor;
}

const QCursor &freeTransformRotateCursor()
{
    static QCursor cursor = makeFreeTransformRotateCursor();
    return cursor;
}

const QCursor &colorPickerCursor()
{
    // Sampling must not inherit the brush's size-ring cursor.  A plain cross
    // marks the exact pixel without obscuring the colour under it.
    static QCursor cursor(Qt::CrossCursor);
    return cursor;
}

Qt::CursorShape freeTransformHandleCursorShape(int handleIndex)
{
    switch (handleIndex) {
    case 0:
    case 4:
        return Qt::SizeFDiagCursor;
    case 2:
    case 6:
        return Qt::SizeBDiagCursor;
    case 1:
    case 5:
        return Qt::SizeVerCursor;
    case 3:
    case 7:
        return Qt::SizeHorCursor;
    default:
        return Qt::SizeAllCursor;
    }
}
}

DrawingCanvas::DrawingCanvas(QWidget *parent)
    : QWidget(parent), m_paintTileCoordinator(this)
{
    setAttribute(Qt::WA_StaticContents);
    setAttribute(Qt::WA_TranslucentBackground, false);
    setAutoFillBackground(true);
    setMouseTracking(true);
    setTabletTracking(true);
    setMinimumSize(96, 96);
    setDocumentSize(QSize(1024, 1024));

    m_maskBlinkFrameTimer.setInterval(16);
    QObject::connect(&m_maskBlinkFrameTimer, &QTimer::timeout, this, [this]() {
        if (!m_maskBlinkActive) {
            m_maskBlinkFrameTimer.stop();
            return;
        }
        if (m_maskBlinkElapsed.elapsed() >= m_maskBlinkDurationMs) {
            m_maskBlinkActive = false;
            m_maskBlinkFrameTimer.stop();
        }
        update();
    });

    m_selectionAntsTimer.setInterval(90);
    QObject::connect(&m_selectionAntsTimer, &QTimer::timeout, this, [this]() {
        if (!hasSelectionRegion() && m_selectionWorkingPoints.isEmpty() && !m_selectionTranslationActive) {
            return;
        }
        m_selectionAntsDashOffset += 0.6;
        if (m_selectionAntsDashOffset >= 8.0) {
            m_selectionAntsDashOffset = std::fmod(m_selectionAntsDashOffset, 8.0);
        }
        update();
    });

    m_2dPreviewFrameTimer.setSingleShot(true);
    m_2dPreviewFrameTimer.setInterval(16);
    QObject::connect(&m_2dPreviewFrameTimer, &QTimer::timeout, this, [this]() {
        if (!m_isDrawing) return;
        flushDeferred2dStrokePreview();
        update();
    });
    QObject::connect(&m_async2dWatcher, &QFutureWatcher<QVector<AsyncDabResult>>::finished, this, [this]() {
        // finishAsync2dStroke() can consume a completed future synchronously.
        if (!m_async2dWorkerBusy) return;
        m_async2dWorkerBusy = false;
        for (AsyncDabResult &result : m_async2dWatcher.result()) acceptAsync2dDab(std::move(result));
        startNextAsync2dDab();
    });
    m_paintTileCoordinator.onReady = [this](const PaintTileCoordinator::BatchResult &result) {
        commitPaintCoreTiles(result);
    };
}

void DrawingCanvas::setTool(Tool tool)
{
    m_tool = tool;
}

void DrawingCanvas::clearCanvas()
{
    ensureLayers();
    if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()
        && (isRasterLayerEffectivelyLocked(m_activeLayerIndex) || !isLayerEffectivelyVisible(m_activeLayerIndex))) {
        return;
    }
    QImage *layer = activeLayerImage();
    if (!layer) {
        return;
    }
    pushUndoHistoryState();
    layer->fill(Qt::white);
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setDocumentSize(const QSize &size)
{
    invalidateAsync2dDabs();
    if (!m_layers.isEmpty()) {
        pushUndoHistoryState();
    }
    const int w = qMax(8, size.width());
    const int h = qMax(8, size.height());
    m_documentSize = QSize(w, h);

    RasterLayer fillLayer;
    fillLayer.layerId = "fill_1";
    fillLayer.name = L("layers.fill_default", "Fill");
    fillLayer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    fillLayer.image.fill(Qt::white);
    fillLayer.maskImage = QImage();
    fillLayer.maskEnabled = false;
    fillLayer.type = "fill";
    fillLayer.parentIndex = -1;
    fillLayer.blendMode = "normal";
    fillLayer.visible = true;
    fillLayer.opacityPercent = 100;
    fillLayer.locked = true;
    fillLayer.expanded = false;

    RasterLayer rasterLayer;
    rasterLayer.layerId = "layer_1";
    rasterLayer.name = L("layer.default_name", "레이어 1");
    rasterLayer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    rasterLayer.image.fill(Qt::transparent);
    rasterLayer.maskImage = QImage();
    rasterLayer.maskEnabled = false;
    rasterLayer.type = "raster";
    rasterLayer.parentIndex = -1;
    rasterLayer.blendMode = "normal";
    rasterLayer.visible = true;
    rasterLayer.opacityPercent = 100;
    rasterLayer.locked = false;
    rasterLayer.expanded = false;

    m_layers = {fillLayer, rasterLayer};
    m_activeLayerIndex = 1;
    bumpContentRevision();
    rebuildUvClipRegion();
    clearSelectionStateHard(false);
    resize(m_documentSize);
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

QSize DrawingCanvas::documentSize() const
{
    return m_documentSize;
}

void DrawingCanvas::setTilingPreviewEnabled(bool enabled)
{
    if (m_tilingPreviewEnabled == enabled) {
        return;
    }
    if (m_isDrawing) {
        endStroke();
    }
    m_tilingPreviewEnabled = enabled;
    m_tilingPreviewUpdateTimer.invalidate();
    forceHideBrushCursor();
    update();
}

bool DrawingCanvas::tilingPreviewEnabled() const
{
    return m_tilingPreviewEnabled;
}

void DrawingCanvas::setCanvasImage(const QImage &image)
{
    if (image.isNull()) {
        return;
    }
    invalidateAsync2dDabs();

    if (!m_layers.isEmpty()) {
        pushUndoHistoryState();
    }

    m_documentSize = image.size();

    RasterLayer fillLayer;
    fillLayer.layerId = "fill_1";
    fillLayer.name = L("layers.fill_default", "Fill");
    fillLayer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    fillLayer.image.fill(Qt::white);
    fillLayer.maskImage = QImage();
    fillLayer.maskEnabled = false;
    fillLayer.type = "fill";
    fillLayer.parentIndex = -1;
    fillLayer.blendMode = "normal";
    fillLayer.visible = true;
    fillLayer.opacityPercent = 100;
    fillLayer.locked = true;
    fillLayer.expanded = false;

    RasterLayer rasterLayer;
    rasterLayer.layerId = "layer_1";
    rasterLayer.name = L("layer.default_name", "레이어 1");
    rasterLayer.image = m_grayscaleOnly ? grayscaleImagePreservingAlpha(image)
                                        : image.convertToFormat(QImage::Format_ARGB32_Premultiplied);
    rasterLayer.maskImage = QImage();
    rasterLayer.maskEnabled = false;
    rasterLayer.type = "raster";
    rasterLayer.parentIndex = -1;
    rasterLayer.blendMode = "normal";
    rasterLayer.visible = true;
    rasterLayer.opacityPercent = 100;
    rasterLayer.locked = false;
    rasterLayer.expanded = false;
    m_layers = {fillLayer, rasterLayer};
    m_activeLayerIndex = 1;
    bumpContentRevision();
    rebuildUvClipRegion();
    clearSelectionStateHard(false);

    resize(m_documentSize);
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

QImage DrawingCanvas::canvasImage() const
{
    return composeLayers();
}

QImage DrawingCanvas::compositedImageRegion(const QRect &requestedRegion) const
{
    const QRect region = requestedRegion.intersected(QRect(QPoint(0, 0), m_documentSize));
    if (region.isEmpty()) return QImage();
    return composeLayersRegion(region);
}

QVector<QRect> DrawingCanvas::strokeDirtyRegions() const
{
    if (m_strokeDirtyTiles.isEmpty())
        return m_strokeDirtyRect.isEmpty() ? QVector<QRect>() : QVector<QRect>{m_strokeDirtyRect};
    QRegion region;
    const QRect document(QPoint(),m_documentSize);
    for (const QPoint &tile : m_strokeDirtyTiles)
        region += QRect(tile * 128,QSize(128,128)).intersected(document);
    QVector<QRect> result;
    result.reserve(region.rectCount());
    for (const QRect &rect : region) result.push_back(rect);
    return result;
}

void DrawingCanvas::clearStrokeDirtyRect()
{
    m_strokeDirtyRect = QRect();
    m_strokeDirtyTiles.clear();
    if (!m_externalUvStrokeActive) {
        return;
    }

    // The 2D canvas is deliberately frozen during a 3D viewport stroke while
    // the viewport receives each small composited patch. Keeping a union of
    // every patch for the 2D composite cache makes that deferred calculation
    // grow for the entire stroke. Drop the stale cache instead; the finished
    // layer stack will be composed once after the external stroke ends.
    m_pendingCompositeDirtyRect = QRect();
    m_pendingCompositeDamageRegion = QRegion();
    m_pendingProjectedCompositeRegion = QRegion();
    m_incrementalCompositeCacheActive = false;
    m_composedCache = QImage();
    m_composedCacheRevision = 0;
}

QVector<DrawingCanvas::RasterLayer> DrawingCanvas::rasterLayers() const
{
    return m_layers;
}

void DrawingCanvas::setRasterLayers(const QVector<RasterLayer> &layers, int activeLayerIndex,
                                    bool pushHistory)
{
    if (pushHistory && !m_layers.isEmpty()) {
        pushUndoHistoryState();
    }
    // Group-cache keys use the in-memory row index. A complete replacement is
    // also used for drag reorder/reparent operations, so an entry at a reused
    // index may describe a different folder even when its local signature
    // happens to match. Keep the retained cache for ordinary paint edits, but
    // never carry it across a new layer tree.
    m_groupCompositeCaches.clear();
    m_composedCache = QImage();
    m_composedCacheRevision = std::numeric_limits<quint64>::max();
    m_layers.clear();
    // Keep the hierarchy valid even when an import or a transient operation
    // contains discarded entries.  Parent indices are positional, so they
    // must be rebuilt whenever the incoming vector is filtered.
    QVector<int> sourceToStored(layers.size(), -1);
    QVector<int> storedToSource;
    storedToSource.reserve(layers.size());
    int layerOrdinal = 1;
    for (int sourceIndex = 0; sourceIndex < layers.size(); ++sourceIndex) {
        const RasterLayer &src = layers.at(sourceIndex);
        RasterLayer layer = src;
        const QString layerType = src.type.trimmed().isEmpty() ? QStringLiteral("raster") : src.type.trimmed().toLower();
        if (src.image.isNull()) {
            if (!isGroupLayerType(layerType)) {
                continue;
            }
            layer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
            layer.image.fill(Qt::transparent);
        } else {
            layer.image = m_grayscaleOnly ? grayscaleImagePreservingAlpha(src.image)
                                          : src.image.convertToFormat(QImage::Format_ARGB32_Premultiplied);
        }
        if (layer.layerId.trimmed().isEmpty()) {
            layer.layerId = QString("layer_%1").arg(layerOrdinal);
        }
        layer.visible = src.visible;
        layer.opacityPercent = qBound(0, src.opacityPercent, 100);
        layer.maskEnabled = src.maskEnabled && !src.maskImage.isNull();
        if (!src.maskImage.isNull()) {
            layer.maskImage = src.maskImage.convertToFormat(QImage::Format_Grayscale8);
            if (layer.maskImage.size() != layer.image.size()) {
                layer.maskImage = layer.maskImage.scaled(layer.image.size(), Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
            }
        } else {
            layer.maskImage = QImage();
        }
        if (layer.name.trimmed().isEmpty()) {
            if (isGroupLayerType(layerType)) {
                layer.name = QString("%1 %2").arg(L("layers.group_base", "그룹")).arg(layerOrdinal);
            } else {
                layer.name = QString("%1 %2").arg(L("layer.base_name", "레이어")).arg(layerOrdinal);
            }
        }
        layer.type = layerType;
        layer.parentIndex = -1;
        layer.blendMode = src.blendMode.trimmed().isEmpty() ? QString("normal") : src.blendMode.trimmed().toLower();
        layer.locked = src.locked;
        layer.transparentPixelsLocked = src.transparentPixelsLocked;
        layer.expanded = src.expanded;
        sourceToStored[sourceIndex] = m_layers.size();
        storedToSource.push_back(sourceIndex);
        m_layers.push_back(layer);
        ++layerOrdinal;
    }

    if (m_layers.isEmpty()) {
        setDocumentSize(m_documentSize);
        return;
    }

    for (int storedIndex = 0; storedIndex < m_layers.size(); ++storedIndex) {
        const int sourceIndex = storedToSource.at(storedIndex);
        const int sourceParent = layers.at(sourceIndex).parentIndex;
        if (sourceParent >= 0 && sourceParent < sourceToStored.size()) {
            const int storedParent = sourceToStored.at(sourceParent);
            if (storedParent >= 0 && storedParent < m_layers.size()
                && isGroupLayerType(m_layers.at(storedParent).type)) {
                m_layers[storedIndex].parentIndex = storedParent;
            }
        }
    }
    // Break malformed cycles rather than allowing a normal layer to inherit a
    // group-only tree role through stale parent indices.
    for (int index = 0; index < m_layers.size(); ++index) {
        int cursor = m_layers.at(index).parentIndex;
        for (int depth = 0; cursor >= 0 && cursor < m_layers.size() && depth < m_layers.size(); ++depth) {
            if (cursor == index) {
                m_layers[index].parentIndex = -1;
                break;
            }
            cursor = m_layers.at(cursor).parentIndex;
        }
    }

    m_documentSize = m_layers[0].image.size();
    int mappedActiveIndex = activeLayerIndex >= 0 && activeLayerIndex < sourceToStored.size()
                                ? sourceToStored.at(activeLayerIndex)
                                : -1;
    if (mappedActiveIndex < 0) {
        mappedActiveIndex = qBound(0, activeLayerIndex, m_layers.size() - 1);
    }
    m_activeLayerIndex = mappedActiveIndex;
    bumpContentRevision();
    rebuildUvClipRegion();
    clearSelectionStateHard(false);
    resize(m_documentSize);
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

int DrawingCanvas::activeRasterLayerIndex() const
{
    return m_activeLayerIndex;
}

bool DrawingCanvas::isRasterLayerEffectivelyVisible(int index) const
{
    return isLayerEffectivelyVisible(index);
}

bool DrawingCanvas::isRasterLayerEffectivelyLocked(int index) const
{
    int current = index;
    for (int depth = 0; depth < m_layers.size(); ++depth) {
        if (current < 0) return false;
        if (current >= m_layers.size()) return true;
        const RasterLayer &layer = m_layers.at(current);
        if (layer.locked) return true;
        if (layer.parentIndex == current) return true;
        current = layer.parentIndex;
    }
    return true;
}

QImage DrawingCanvas::rasterLayerPreviewImage(int index) const
{
    if (index < 0 || index >= m_layers.size()) return QImage();
    QImage raw = composeLayerSubtree(index);
    if (raw.isNull()) return raw;
    QImage result(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    result.fill(Qt::transparent);
    QPainter painter(&result);
    painter.setOpacity(qBound(0.0, m_layers.at(index).opacityPercent / 100.0, 1.0));
    painter.drawImage(QPoint(0, 0), raw);
    return result;
}

void DrawingCanvas::setActiveRasterLayerIndex(int index)
{
    if (m_layers.isEmpty()) {
        return;
    }
    int clamped = qBound(0, index, m_layers.size() - 1);
    if (clamped == m_activeLayerIndex) {
        return;
    }
    m_activeLayerIndex = clamped;
    if (isFreeTransformMode()) {
        resetFreeTransformSession();
        if (m_selectionToolEnabled && hasSelectionRegion()) {
            refreshFreeTransformSession();
        }
    }
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::addRasterLayer(const QString &name)
{
    ensureLayers();
    pushUndoHistoryState();
    RasterLayer layer;
    layer.layerId = QString("layer_%1").arg(m_layers.size() + 1);
    layer.name = name.trimmed().isEmpty() ? L("layer.default_name", "레이어 1") : name.trimmed();
    layer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    layer.image.fill(Qt::transparent);
    layer.maskImage = QImage();
    layer.maskEnabled = false;
    layer.type = "raster";
    int parentIndex = -1;
    int insertIndex = m_layers.size();
    if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        const RasterLayer &active = m_layers.at(m_activeLayerIndex);
        parentIndex = active.parentIndex;
        insertIndex = qBound(0, m_activeLayerIndex + 1, m_layers.size());
    }

    for (int i = 0; i < m_layers.size(); ++i) {
        if (m_layers[i].parentIndex >= insertIndex) {
            m_layers[i].parentIndex += 1;
        }
    }

    if (parentIndex >= insertIndex) {
        parentIndex += 1;
    }
    layer.parentIndex = qBound(-1, parentIndex, m_layers.size());
    layer.blendMode = "normal";
    layer.visible = true;
    layer.opacityPercent = 100;
    layer.locked = false;
    layer.expanded = false;
    m_layers.insert(insertIndex, layer);
    m_activeLayerIndex = insertIndex;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::addFillLayer(const QString &name, const QColor &color)
{
    ensureLayers();
    pushUndoHistoryState();

    RasterLayer layer;
    layer.layerId = QString("fill_%1").arg(m_layers.size() + 1);
    layer.name = name.trimmed().isEmpty() ? L("layers.fill_default", "Fill") : name.trimmed();
    layer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    QColor fill = color.isValid() ? color : QColor(Qt::white);
    if (m_grayscaleOnly) fill = QColor(qGray(fill.rgb()), qGray(fill.rgb()), qGray(fill.rgb()), fill.alpha());
    layer.image.fill(fill);
    layer.maskImage = QImage();
    layer.maskEnabled = false;
    layer.type = "fill";
    int parentIndex = -1;
    int insertIndex = m_layers.size();
    if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        const RasterLayer &active = m_layers.at(m_activeLayerIndex);
        parentIndex = active.parentIndex;
        insertIndex = qBound(0, m_activeLayerIndex + 1, m_layers.size());
    }

    for (int i = 0; i < m_layers.size(); ++i) {
        if (m_layers[i].parentIndex >= insertIndex) {
            m_layers[i].parentIndex += 1;
        }
    }

    if (parentIndex >= insertIndex) {
        parentIndex += 1;
    }
    layer.parentIndex = qBound(-1, parentIndex, m_layers.size());
    layer.blendMode = "normal";
    layer.visible = true;
    layer.opacityPercent = 100;
    layer.locked = false;
    layer.expanded = false;
    m_layers.insert(insertIndex, layer);
    m_activeLayerIndex = insertIndex;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::removeActiveRasterLayer()
{
    ensureLayers();
    int rasterCount = 0;
    for (const RasterLayer &layer : m_layers) {
        if (!isGroupLayerType(layer.type)) {
            ++rasterCount;
        }
    }

    const bool removingRaster = !isGroupLayerType(m_layers[m_activeLayerIndex].type);
    if (removingRaster && rasterCount <= 1) {
        return;
    }

    pushUndoHistoryState();

    const int removedIndex = m_activeLayerIndex;
    int inheritedParent = m_layers[removedIndex].parentIndex;
    if (inheritedParent == removedIndex) {
        inheritedParent = -1;
    }

    m_layers.removeAt(m_activeLayerIndex);
    if (inheritedParent > removedIndex) {
        --inheritedParent;
    }

    for (int i = 0; i < m_layers.size(); ++i) {
        RasterLayer &layer = m_layers[i];
        if (layer.parentIndex == removedIndex) {
            layer.parentIndex = inheritedParent;
        } else if (layer.parentIndex > removedIndex) {
            --layer.parentIndex;
        }
        if (layer.parentIndex == i) {
            layer.parentIndex = -1;
        }
    }

    m_activeLayerIndex = qBound(0, m_activeLayerIndex, m_layers.size() - 1);
    if (isGroupLayerType(m_layers[m_activeLayerIndex].type)) {
        int resolved = m_activeLayerIndex;
        for (int d = 1; d < m_layers.size(); ++d) {
            const int down = m_activeLayerIndex - d;
            if (down >= 0 && !isGroupLayerType(m_layers[down].type)) {
                resolved = down;
                break;
            }
            const int up = m_activeLayerIndex + d;
            if (up < m_layers.size() && !isGroupLayerType(m_layers[up].type)) {
                resolved = up;
                break;
            }
        }
        m_activeLayerIndex = resolved;
    }

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerVisible(int index, bool visible)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }
    if (m_layers[index].visible == visible) {
        return;
    }
    pushUndoHistoryState();
    m_layers[index].visible = visible;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerOpacityPercent(int index, int opacityPercent)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }
    const int clamped = qBound(0, opacityPercent, 100);
    if (m_layers[index].opacityPercent == clamped) {
        return;
    }
    pushUndoHistoryState();
    m_layers[index].opacityPercent = clamped;

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerBlendMode(int index, const QString &blendMode)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }
    const QString normalized = blendMode.trimmed().isEmpty()
                                   ? QStringLiteral("normal")
                                   : blendMode.trimmed().toLower();
    if (normalized == QStringLiteral("pass_through") && !isGroupLayerType(m_layers.at(index).type)) {
        return;
    }
    if (m_layers[index].blendMode == normalized) {
        return;
    }
    pushUndoHistoryState();
    m_layers[index].blendMode = normalized;

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerSolidColor(int index, const QColor &color, bool pushHistory)
{
    if (index < 0 || index >= m_layers.size() || !color.isValid()) {
        return;
    }
    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    QColor normalizedColor = color;
    if (m_grayscaleOnly) {
        const int gray = qGray(color.rgb());
        normalizedColor = QColor(gray, gray, gray, color.alpha());
    }
    if (pushHistory) {
        pushUndoHistoryState();
    }
    RasterLayer &layer = m_layers[index];
    if (layer.transparentPixelsLocked) {
        QPainter painter(&layer.image);
        painter.setCompositionMode(QPainter::CompositionMode_SourceAtop);
        painter.fillRect(layer.image.rect(), normalizedColor);
        painter.end();
    } else {
        layer.image.fill(normalizedColor);
    }
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::renameRasterLayer(int index, const QString &name)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }
    const QString trimmed = name.trimmed();
    if (trimmed.isEmpty() || m_layers[index].name == trimmed) {
        return;
    }
    m_layers[index].name = trimmed;
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
}

bool DrawingCanvas::beginLayerImagePreview(int index)
{
    if (index < 0 || index >= m_layers.size()) {
        return false;
    }
    if (isGroupLayerType(m_layers.at(index).type) || m_layers.at(index).locked
        || !isLayerEffectivelyVisible(index) || m_layers.at(index).image.isNull()) {
        return false;
    }

    m_layerImagePreviewActive = true;
    m_layerImagePreviewIndex = index;
    m_layerImagePreviewOriginalImage = m_layers.at(index).image;
    return true;
}

void DrawingCanvas::updateLayerImagePreview(const QImage &image)
{
    if (!m_layerImagePreviewActive || m_layerImagePreviewIndex < 0 || m_layerImagePreviewIndex >= m_layers.size()) {
        return;
    }
    if (!isLayerEffectivelyVisible(m_layerImagePreviewIndex)) {
        return;
    }
    if (image.isNull()) {
        return;
    }

    QImage normalized = image.convertToFormat(QImage::Format_ARGB32_Premultiplied);
    if (normalized.size() != m_layers.at(m_layerImagePreviewIndex).image.size()) {
        normalized = normalized.scaled(m_layers.at(m_layerImagePreviewIndex).image.size(),
                                       Qt::IgnoreAspectRatio,
                                       Qt::SmoothTransformation);
    }
    m_layers[m_layerImagePreviewIndex].image = normalized;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::commitLayerImagePreview()
{
    if (!m_layerImagePreviewActive || m_layerImagePreviewIndex < 0 || m_layerImagePreviewIndex >= m_layers.size()) {
        return;
    }

    const QImage committed = m_layers.at(m_layerImagePreviewIndex).image;
    const bool changed = committed != m_layerImagePreviewOriginalImage;

    if (changed) {
        m_layers[m_layerImagePreviewIndex].image = m_layerImagePreviewOriginalImage;
        pushUndoHistoryState();
        m_layers[m_layerImagePreviewIndex].image = committed;
        bumpContentRevision();
        if (onLayerStackChanged) {
            onLayerStackChanged();
        }
        update();
    }

    m_layerImagePreviewActive = false;
    m_layerImagePreviewIndex = -1;
    m_layerImagePreviewOriginalImage = QImage();
}

void DrawingCanvas::cancelLayerImagePreview()
{
    if (!m_layerImagePreviewActive || m_layerImagePreviewIndex < 0 || m_layerImagePreviewIndex >= m_layers.size()) {
        return;
    }

    m_layers[m_layerImagePreviewIndex].image = m_layerImagePreviewOriginalImage;
    m_layerImagePreviewActive = false;
    m_layerImagePreviewIndex = -1;
    m_layerImagePreviewOriginalImage = QImage();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

bool DrawingCanvas::rasterLayerHasMask(int index) const
{
    if (index < 0 || index >= m_layers.size()) {
        return false;
    }
    const RasterLayer &layer = m_layers[index];
    return !layer.maskImage.isNull();
}

bool DrawingCanvas::rasterLayerMaskEnabled(int index) const
{
    if (index < 0 || index >= m_layers.size()) {
        return false;
    }
    return m_layers[index].maskEnabled;
}

QImage DrawingCanvas::rasterLayerMaskImage(int index) const
{
    if (index < 0 || index >= m_layers.size()) {
        return QImage();
    }
    return m_layers[index].maskImage;
}

QImage DrawingCanvas::activeMaskPaintPreviewImage() const
{
    if (m_maskPaintingEnabled && m_isDrawing && !m_maskStrokePreviewImage.isNull()) {
        return m_maskStrokePreviewImage;
    }
    return rasterLayerMaskImage(m_activeLayerIndex);
}

void DrawingCanvas::setBucketGradientPreview(const QPointF &startCanvasPoint,
                                              const QPointF &endCanvasPoint,
                                              bool visible)
{
    m_bucketGradientPreviewVisible = visible;
    m_bucketGradientPreviewStart = startCanvasPoint;
    m_bucketGradientPreviewEnd = endCanvasPoint;
    update();
}

bool DrawingCanvas::beginLayerMaskPreview(int index)
{
    if (index < 0 || index >= m_layers.size() || m_layers.at(index).maskImage.isNull()
        || isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return false;
    }
    m_layerMaskPreviewActive = true;
    m_layerMaskPreviewIndex = index;
    m_layerMaskPreviewOriginalImage = m_layers.at(index).maskImage;
    return true;
}

void DrawingCanvas::updateLayerMaskPreview(const QImage &maskImage)
{
    if (!m_layerMaskPreviewActive || m_layerMaskPreviewIndex < 0
        || m_layerMaskPreviewIndex >= m_layers.size() || maskImage.isNull()) {
        return;
    }
    QImage normalized = maskImage.convertToFormat(QImage::Format_Grayscale8);
    const QSize targetSize = m_layers.at(m_layerMaskPreviewIndex).maskImage.size();
    if (normalized.size() != targetSize) {
        normalized = normalized.scaled(targetSize, Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
    }
    m_layers[m_layerMaskPreviewIndex].maskImage = normalized;
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
}

void DrawingCanvas::commitLayerMaskPreview()
{
    if (!m_layerMaskPreviewActive || m_layerMaskPreviewIndex < 0
        || m_layerMaskPreviewIndex >= m_layers.size()) {
        return;
    }
    const QImage committed = m_layers.at(m_layerMaskPreviewIndex).maskImage;
    if (committed != m_layerMaskPreviewOriginalImage) {
        m_layers[m_layerMaskPreviewIndex].maskImage = m_layerMaskPreviewOriginalImage;
        pushUndoHistoryState();
        m_layers[m_layerMaskPreviewIndex].maskImage = committed;
        bumpContentRevision();
        if (onLayerStackChanged) onLayerStackChanged();
        update();
    }
    m_layerMaskPreviewActive = false;
    m_layerMaskPreviewIndex = -1;
    m_layerMaskPreviewOriginalImage = QImage();
}

void DrawingCanvas::cancelLayerMaskPreview()
{
    if (!m_layerMaskPreviewActive || m_layerMaskPreviewIndex < 0
        || m_layerMaskPreviewIndex >= m_layers.size()) {
        return;
    }
    m_layers[m_layerMaskPreviewIndex].maskImage = m_layerMaskPreviewOriginalImage;
    m_layerMaskPreviewActive = false;
    m_layerMaskPreviewIndex = -1;
    m_layerMaskPreviewOriginalImage = QImage();
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
}

QVector<int> DrawingCanvas::rasterLayerMeshMaskFaces(int index) const
{
    if (index < 0 || index >= m_layers.size()) return {};
    return m_layers[index].meshMaskFaceIndices;
}

void DrawingCanvas::ensureRasterLayerMask(int index)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }

    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    const QSize maskSize = layer.image.isNull() ? m_documentSize : layer.image.size();
    if (layer.maskEnabled && !layer.maskImage.isNull() && layer.maskImage.size() == maskSize) {
        return;
    }

    pushUndoHistoryState();

    layer.maskImage = QImage(maskSize, QImage::Format_Grayscale8);
    layer.maskImage.fill(255);
    layer.maskEnabled = true;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::clearRasterLayerMask(int index)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }

    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    if (!layer.maskEnabled && layer.maskImage.isNull()) {
        return;
    }

    pushUndoHistoryState();

    layer.maskEnabled = false;
    layer.maskImage = QImage();
    layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerMaskEnabled(int index, bool enabled)
{
    if (index < 0 || index >= m_layers.size()) {
        return;
    }

    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    const bool needsMaskImageCreation = enabled && layer.maskImage.isNull();
    const bool stateWillChange = (layer.maskEnabled != enabled) || needsMaskImageCreation;
    if (!stateWillChange) {
        return;
    }

    pushUndoHistoryState();

    if (enabled) {
        if (layer.maskImage.isNull()) {
            const QSize maskSize = layer.image.isNull() ? m_documentSize : layer.image.size();
            layer.maskImage = QImage(maskSize, QImage::Format_Grayscale8);
            layer.maskImage.fill(255);
        }
    }

    layer.maskEnabled = enabled;
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::setRasterLayerMaskImage(int index, const QImage &maskImage, bool enabled)
{
    if (index < 0 || index >= m_layers.size() || maskImage.isNull()) {
        return;
    }

    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    QImage normalized = maskImage.convertToFormat(QImage::Format_Grayscale8);
    const QSize targetMaskSize = layer.image.isNull() ? m_documentSize : layer.image.size();
    if (targetMaskSize.isEmpty()) {
        return;
    }
    if (normalized.size() != targetMaskSize) {
        normalized = normalized.scaled(targetMaskSize, Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
    }

    pushUndoHistoryState();

    layer.maskImage = normalized;
    layer.maskEnabled = enabled;
    layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::applyMaskValueToUvFaces(int index,
                                            const QVector<QPointF> &uvPoints,
                                            const QVector<quint32> &indices,
                                            const QVector<int> &triangleIndices,
                                            int grayscaleValue,
                                            bool replaceExisting)
{
    if (index < 0 || index >= m_layers.size() || triangleIndices.isEmpty()) {
        return;
    }

    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)) {
        return;
    }

    const bool hadReadyMask = m_layers[index].maskEnabled
                              && !m_layers[index].maskImage.isNull()
                              && m_layers[index].maskImage.size() == m_layers[index].image.size();
    ensureRasterLayerMask(index);
    RasterLayer &layer = m_layers[index];
    if (layer.maskImage.isNull()) {
        return;
    }

    const int docWm1 = qMax(1, layer.image.width() - 1);
    const int docHm1 = qMax(1, layer.image.height() - 1);
    const int clampedValue = qBound(0, grayscaleValue, 255);

    QRegion faceRegion;

    for (int tri : triangleIndices) {
        if (tri < 0) {
            continue;
        }
        const int base = tri * 3;
        if (base + 2 >= indices.size()) {
            continue;
        }

        const quint32 i0 = indices[base + 0];
        const quint32 i1 = indices[base + 1];
        const quint32 i2 = indices[base + 2];
        if (i0 >= static_cast<quint32>(uvPoints.size())
            || i1 >= static_cast<quint32>(uvPoints.size())
            || i2 >= static_cast<quint32>(uvPoints.size())) {
            continue;
        }

        const auto uvToPixel = [docWm1, docHm1](const QPointF &uv) {
            const qreal u = qBound(0.0, uv.x(), 1.0);
            const qreal v = qBound(0.0, uv.y(), 1.0);
            return QPointF(u * docWm1, (1.0 - v) * docHm1);
        };

        QPolygon polygon;
        polygon << uvToPixel(uvPoints[static_cast<int>(i0)]).toPoint()
                << uvToPixel(uvPoints[static_cast<int>(i1)]).toPoint()
                << uvToPixel(uvPoints[static_cast<int>(i2)]).toPoint();
        faceRegion = faceRegion.united(QRegion(polygon, Qt::WindingFill));
    }

    if (faceRegion.isEmpty()) {
        return;
    }

    // The first face fill may create/initialise a mask.  It still needs the
    // mask-edit undo snapshot; previously that callback only ran when a mask
    // already existed, leaving this fill outside the mask history.
    if (onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (hadReadyMask) {
        pushUndoHistoryState();
    }
    if (replaceExisting) {
        layer.maskImage.fill(255 - clampedValue);
        layer.meshMaskFaceIndices = triangleIndices;
        std::sort(layer.meshMaskFaceIndices.begin(), layer.meshMaskFaceIndices.end());
        layer.meshMaskFaceIndices.erase(
            std::unique(layer.meshMaskFaceIndices.begin(), layer.meshMaskFaceIndices.end()),
            layer.meshMaskFaceIndices.end());
    }

    // Use exactly the same integer UV region as normal face-restricted painting.
    // Binary values avoid partially transparent edge texels mixing the layer color.
    QPainter maskPainter(&layer.maskImage);
    maskPainter.setRenderHint(QPainter::Antialiasing, false);
    maskPainter.setClipRegion(faceRegion);
    maskPainter.fillRect(layer.maskImage.rect(), QColor(clampedValue, clampedValue, clampedValue));
    maskPainter.end();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::applySolidColorToUvFaces(int index,
                                             const QVector<QPointF> &uvPoints,
                                             const QVector<quint32> &indices,
                                             const QVector<int> &triangleIndices,
                                             const QColor &color)
{
    if (index < 0 || index >= m_layers.size() || triangleIndices.isEmpty() || !color.isValid()) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) {
        return;
    }

    const int docWm1 = targetImage->width();
    const int docHm1 = targetImage->height();

    QPainterPath fillPath;
    fillPath.setFillRule(Qt::WindingFill);
    for (int tri : triangleIndices) {
        if (tri < 0) {
            continue;
        }
        const int base = tri * 3;
        if (base + 2 >= indices.size()) {
            continue;
        }

        const quint32 i0 = indices[base + 0];
        const quint32 i1 = indices[base + 1];
        const quint32 i2 = indices[base + 2];
        if (i0 >= static_cast<quint32>(uvPoints.size())
            || i1 >= static_cast<quint32>(uvPoints.size())
            || i2 >= static_cast<quint32>(uvPoints.size())) {
            continue;
        }

        const auto uvToPixel = [docWm1, docHm1](const QPointF &uv) {
            const qreal u = qBound(0.0, uv.x(), 1.0);
            const qreal v = qBound(0.0, uv.y(), 1.0);
            return QPointF(u * docWm1, (1.0 - v) * docHm1);
        };

        QPointF a = uvToPixel(uvPoints[static_cast<int>(i0)]);
        QPointF b = uvToPixel(uvPoints[static_cast<int>(i1)]);
        QPointF c = uvToPixel(uvPoints[static_cast<int>(i2)]);
        QPainterPath triPath;
        triPath.moveTo(a);
        triPath.lineTo(b);
        triPath.lineTo(c);
        triPath.closeSubpath();
        if ((b.x() - a.x()) * (c.y() - a.y()) - (b.y() - a.y()) * (c.x() - a.x()) < 0.0) {
            triPath = triPath.toReversed();
        }
        fillPath.addPath(triPath);
    }

    if (fillPath.isEmpty()) {
        return;
    }

    const QRegion fillRegion = paddedUvFillRegion(fillPath, targetImage->size());

    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (!editingMask && !m_historyTransactionActive) pushUndoHistoryState();
    QPainter painter(targetImage);
    painter.setRenderHint(QPainter::Antialiasing, false);
    if (!editingMask && layer.transparentPixelsLocked) {
        painter.setCompositionMode(QPainter::CompositionMode_SourceAtop);
    } else if (color.alpha() == 0) {
        // Transparent bucket fills erase the target UV area instead of
        // source-over compositing a no-op transparent colour.
        painter.setCompositionMode(QPainter::CompositionMode_Source);
    }
    painter.setClipRegion(fillRegion, Qt::IntersectClip);
    const QColor paintColor = editingMask
                                  ? QColor(qGray(color.rgb()), qGray(color.rgb()), qGray(color.rgb()))
                                  : color;
    painter.fillRect(targetImage->rect(), paintColor);
    painter.end();
    if (editingMask) layer.meshMaskFaceIndices.clear();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::applyGradientToUvFaces(int index,
                                           const QVector<QPointF> &uvPoints,
                                           const QVector<quint32> &indices,
                                           const QVector<int> &triangleIndices,
                                           const QPointF &startUv,
                                           const QPointF &endUv,
                                           const QColor &startColor,
                                           const QColor &endColor)
{
    if (index < 0 || index >= m_layers.size() || triangleIndices.isEmpty() || !startColor.isValid() || !endColor.isValid()) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) {
        return;
    }

    const int docWm1 = targetImage->width();
    const int docHm1 = targetImage->height();
    const auto uvToPixel = [docWm1, docHm1](const QPointF &uv) {
        const qreal u = qBound(0.0, uv.x(), 1.0);
        const qreal v = qBound(0.0, uv.y(), 1.0);
        return QPointF(u * docWm1, (1.0 - v) * docHm1);
    };

    QPainterPath fillPath;
    // Keep overlapping UV triangles as one continuous painted region.  This
    // also prevents the same seam artifact for gradient bucket fills.
    fillPath.setFillRule(Qt::WindingFill);
    for (int tri : triangleIndices) {
        if (tri < 0) {
            continue;
        }
        const int base = tri * 3;
        if (base + 2 >= indices.size()) {
            continue;
        }

        const quint32 i0 = indices[base + 0];
        const quint32 i1 = indices[base + 1];
        const quint32 i2 = indices[base + 2];
        if (i0 >= static_cast<quint32>(uvPoints.size())
            || i1 >= static_cast<quint32>(uvPoints.size())
            || i2 >= static_cast<quint32>(uvPoints.size())) {
            continue;
        }

        const QPointF first = uvToPixel(uvPoints[static_cast<int>(i0)]);
        const QPointF second = uvToPixel(uvPoints[static_cast<int>(i1)]);
        const QPointF third = uvToPixel(uvPoints[static_cast<int>(i2)]);
        QPainterPath triPath;
        triPath.moveTo(first);
        triPath.lineTo(second);
        triPath.lineTo(third);
        triPath.closeSubpath();
        if ((second.x() - first.x()) * (third.y() - first.y())
            - (second.y() - first.y()) * (third.x() - first.x()) < 0.0) {
            triPath = triPath.toReversed();
        }
        fillPath.addPath(triPath);
    }

    if (fillPath.isEmpty()) {
        return;
    }

    const QRegion fillRegion = paddedUvFillRegion(fillPath, targetImage->size());

    QPointF startPx = uvToPixel(startUv);
    QPointF endPx = uvToPixel(endUv);
    if (QLineF(startPx, endPx).length() < 0.001) {
        endPx += QPointF(layer.image.width(), 0.0);
    }

    QLinearGradient gradient(startPx, endPx);
    const QColor gradientStart = editingMask
                                     ? QColor(qGray(startColor.rgb()), qGray(startColor.rgb()), qGray(startColor.rgb()))
                                     : startColor;
    const QColor gradientEnd = editingMask
                                   ? QColor(qGray(endColor.rgb()), qGray(endColor.rgb()), qGray(endColor.rgb()))
                                   : endColor;
    gradient.setColorAt(0.0, gradientStart);
    gradient.setColorAt(1.0, gradientEnd);

    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (!editingMask) pushUndoHistoryState();
    QPainter painter(targetImage);
    painter.setRenderHint(QPainter::Antialiasing, false);
    painter.setClipRegion(fillRegion, Qt::IntersectClip);
    painter.fillRect(targetImage->rect(), gradient);
    painter.end();
    if (editingMask) layer.meshMaskFaceIndices.clear();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::beginExternalUvStroke(const QPointF &uv, qreal pressure)
{
    ensureLayers();
    // Keep the 2D view frozen at the correctly ordered pre-stroke composite.
    // The 3D stroke still updates its own texture path; 2D is refreshed only
    // after endExternalUvStroke commits the finished layer stack.
    m_externalStrokeDisplayImage = (!m_composedCache.isNull()
                                    && m_composedCacheRevision == m_contentRevision)
                                       ? m_composedCache
                                       : composeLayers();
    m_externalUvStrokeActive = true;
    m_suppressExternalStrokeDisplay = true;
    if (m_projectedStampProvider) {
        beginStroke(uv, qBound(0.05, pressure, 1.0));
        return;
    }
    const qreal u = qBound(0.0, uv.x(), 1.0);
    const qreal v = qBound(0.0, uv.y(), 1.0);
    const QPointF canvasPoint(
        u * qMax(1, m_documentSize.width() - 1),
        (1.0 - v) * qMax(1, m_documentSize.height() - 1));
    m_externalUvIslandIndex = -1;
    updateExternalUvIsland(canvasPoint);
    beginStroke(canvasPoint, qBound(0.05, pressure, 1.0));
}

void DrawingCanvas::continueExternalUvStroke(const QPointF &uv, qreal pressure)
{
    if (!m_isDrawing) {
        beginExternalUvStroke(uv, pressure);
        return;
    }

    if (m_projectedStampProvider) {
        continueStroke(uv, qBound(0.05, pressure, 1.0));
        return;
    }

    const qreal u = qBound(0.0, uv.x(), 1.0);
    const qreal v = qBound(0.0, uv.y(), 1.0);
    const QPointF canvasPoint(
        u * qMax(1, m_documentSize.width() - 1),
        (1.0 - v) * qMax(1, m_documentSize.height() - 1));
    const qreal clampedPressure = qBound(0.05, pressure, 1.0);

    // 3D surface continuity can jump across distant UV islands.
    // If the UV-mapped point teleports too far, restart dabbing from the new point
    // instead of drawing a long straight segment that contaminates unrelated texels.
    const QPointF delta = canvasPoint - m_lastPoint;
    const qreal jump = std::hypot(delta.x(), delta.y());
    const qreal docScaleThreshold = qMax(m_documentSize.width(), m_documentSize.height()) * 0.08;
    const qreal brushScaleThreshold = brushPreviewRadiusPx(clampedPressure) * 8.0;
    const qreal seamSplitThreshold = qMax(24.0, qMax(docScaleThreshold, brushScaleThreshold));
    if (updateExternalUvIsland(canvasPoint) || jump > seamSplitThreshold) {
        beginStroke(canvasPoint, clampedPressure);
        return;
    }

    continueStroke(canvasPoint, clampedPressure);
}

void DrawingCanvas::setExternalProjection(ProjectedStampProvider provider, qreal screenScale,
                                          const QPointF &symmetryCenter, qreal spacingScale)
{
    m_projectedStampProvider = std::move(provider);
    m_projectedStrokeScale = qMax(0.01, screenScale);
    m_projectedSpacingScale = qMax(0.01, spacingScale);
    m_projectedSymmetryCenter = symmetryCenter;
}

void DrawingCanvas::setProjectedStampBatchProvider(ProjectedStampBatchProvider provider)
{
    m_projectedStampBatchProvider = std::move(provider);
}

void DrawingCanvas::setProjectedSurfaceSpacingProviders(ProjectedSurfaceHitProvider hitProvider,
                                                        ProjectedWorldProjector projector)
{
    m_projectedSurfaceHitProvider = std::move(hitProvider);
    m_projectedWorldProjector = std::move(projector);
    m_projectedSceneSpacingActive = false;
}

void DrawingCanvas::setProjectedCompositeObserver(ProjectedCompositeObserver observer)
{
    m_projectedCompositeObserver = std::move(observer);
}

void DrawingCanvas::setProjectedStrokeObserver(ProjectedStrokeObserver observer)
{
    m_projectedStrokeObserver = std::move(observer);
}

void DrawingCanvas::setExperimentalGpuStrokeCallbacks(ExperimentalGpuStrokeBegin begin,
                                                       ExperimentalGpuStrokeSubmit submit,
                                                       ExperimentalGpuStrokeFinish finish,
                                                       ExperimentalGpuStrokeDamage damage)
{
    m_experimentalGpuStrokeBegin = std::move(begin);
    m_experimentalGpuStrokeSubmit = std::move(submit);
    m_experimentalGpuStrokeFinish = std::move(finish);
    m_experimentalGpuStrokeDamage = std::move(damage);
}

bool DrawingCanvas::gpuStrokePreviewLayers(QImage *background, QImage *foreground,
                                           QImage *mask, qreal *opacity)
{
    if (!background || !foreground || !mask || !opacity || m_maskPaintingEnabled
        || m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) return false;
    const RasterLayer &active = m_layers.at(m_activeLayerIndex);
    if (active.blendMode != QStringLiteral("normal") || active.type != QStringLiteral("raster")
        || !active.textElements.isEmpty()) return false;
    for (int index = 0; index < m_layers.size(); ++index) {
        const RasterLayer &layer = m_layers.at(index);
        if (layer.parentIndex >= 0 || isGroupLayerType(layer.type)) return false;
        if (index > m_activeLayerIndex && layer.visible
            && layer.blendMode != QStringLiteral("normal")) return false;
    }
    const auto composeRange = [&](int first, int last) {
        int visibleCount = 0;
        int visibleIndex = -1;
        for (int index = first; index < last; ++index) {
            if (m_layers.at(index).visible) { ++visibleCount; visibleIndex = index; }
        }
        if (!visibleCount) {
            QImage transparent(1, 1, QImage::Format_ARGB32_Premultiplied);
            transparent.fill(Qt::transparent);
            return transparent;
        }
        if (visibleCount == 1) {
            const RasterLayer &layer = m_layers.at(visibleIndex);
            if (layer.type == QStringLiteral("raster") && layer.textElements.isEmpty()
                && layer.blendMode == QStringLiteral("normal") && layer.opacityPercent == 100
                && (!layer.maskEnabled || layer.maskImage.isNull()) && layer.image.size() == m_documentSize
                && layer.image.format() == QImage::Format_ARGB32_Premultiplied) return layer.image;
        }
        QVector<bool> visibility;
        for (const RasterLayer &layer : std::as_const(m_layers)) visibility.push_back(layer.visible);
        for (int index = 0; index < m_layers.size(); ++index)
            m_layers[index].visible = index >= first && index < last && visibility.at(index);
        const QImage result = composeLayersRegion(QRect(QPoint(), m_documentSize));
        for (int index = 0; index < m_layers.size(); ++index) m_layers[index].visible = visibility.at(index);
        return result;
    };
    *background = composeRange(0, m_activeLayerIndex);
    *foreground = composeRange(m_activeLayerIndex + 1, m_layers.size());
    *mask = active.maskEnabled ? active.maskImage.convertToFormat(QImage::Format_Grayscale8) : QImage();
    if (!mask->isNull() && mask->size() != m_documentSize)
        *mask = mask->scaled(m_documentSize, Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
    *opacity = active.visible ? qBound(0.0, active.opacityPercent / 100.0, 1.0) : 0.0;
    return !background->isNull() && !foreground->isNull();
}

bool DrawingCanvas::canUseGpuLayerCompositor() const
{
    if (m_maskPaintingEnabled || m_layers.isEmpty() || m_activeLayerIndex < 0
        || m_activeLayerIndex >= m_layers.size()) return false;
    // The painted source must remain a direct texture.  Other top-level
    // entries may be groups or text; those are flattened once into retained
    // inputs, so they do not force every brush preview back to CPU compositing.
    const RasterLayer &active = m_layers.at(m_activeLayerIndex);
    if (active.parentIndex >= 0 || active.type != QStringLiteral("raster")
        || !active.textElements.isEmpty() || active.image.size() != m_documentSize) return false;
    if (active.maskEnabled && (!active.maskImage.isNull() && active.maskImage.size() != m_documentSize)) return false;
    return true;
}

bool DrawingCanvas::gpuStrokePreviewLayerStack(QVector<GpuPreviewLayer> *layers) const
{
    if (!layers || !canUseGpuLayerCompositor() || m_activeLayerIndex < 0
        || m_activeLayerIndex >= m_layers.size()) return false;
    layers->clear();
    layers->reserve(m_layers.size());
    for (int index = 0; index < m_layers.size(); ++index) {
        const RasterLayer &source = m_layers.at(index);
        if (source.parentIndex >= 0) continue;
        GpuPreviewLayer layer;
        const bool flattened = isGroupLayerType(source.type) || !source.textElements.isEmpty()
                               || source.type == QStringLiteral("text");
        layer.image = flattened ? composeLayerSubtree(index) : source.image;
        layer.mask = flattened ? QImage() : (source.maskEnabled ? source.maskImage : QImage());
        if (layer.image.size() != m_documentSize) return false;
        layer.opacity = qBound(0.0, source.opacityPercent / 100.0, 1.0);
        layer.visible = source.visible;
        layer.active = index == m_activeLayerIndex;
        const QString blend = source.blendMode.trimmed().toLower();
        if (blend == QStringLiteral("multiply")) layer.blendMode = 1;
        else if (blend == QStringLiteral("screen")) layer.blendMode = 2;
        else if (blend == QStringLiteral("overlay")) layer.blendMode = 3;
        else if (blend == QStringLiteral("darken")) layer.blendMode = 4;
        else if (blend == QStringLiteral("lighten")) layer.blendMode = 5;
        else if (blend == QStringLiteral("plus") || blend == QStringLiteral("add")) layer.blendMode = 6;
        layers->push_back(std::move(layer));
    }
    return true;
}

bool DrawingCanvas::gpuStrokePreviewLayerTree(QVector<GpuPreviewTreeNode> *roots) const
{
    if (!roots || m_activeLayerIndex < 0
        || m_activeLayerIndex >= m_layers.size()) return false;
    std::function<GpuPreviewTreeNode(int)> makeNode = [&](int index) {
        const RasterLayer &source = m_layers.at(index);
        GpuPreviewTreeNode node;
        node.layerId = source.layerId.isEmpty() ? QStringLiteral("layer_%1").arg(index) : source.layerId;
        node.type = source.type;
        node.blendMode = source.blendMode;
        node.opacity = qBound(0.0, source.opacityPercent / 100.0, 1.0);
        node.visible = source.visible;
        node.active = index == m_activeLayerIndex;
        node.mask = source.maskEnabled ? source.maskImage : QImage();
        if (isGroupLayerType(source.type)) {
            for (int child = 0; child < m_layers.size(); ++child)
                if (m_layers.at(child).parentIndex == index) node.children.push_back(makeNode(child));
        } else if (source.type == QStringLiteral("text") || !source.textElements.isEmpty()) {
            // Text is rasterized once when its source signature changes, then
            // retained by the GPU cache like any other leaf texture.
            node.image = composeLayerSubtree(index);
        } else {
            node.image = source.image;
        }
        return node;
    };
    roots->clear();
    for (int index = 0; index < m_layers.size(); ++index)
        if (m_layers.at(index).parentIndex < 0) roots->push_back(makeNode(index));
    return !roots->isEmpty();
}

QImage DrawingCanvas::compositeGpuStrokePreview(const QImage &layerImage)
{
    if (!m_nonAccumulatingStrokeActive || layerImage.size() != m_documentSize) return QImage();
    const QImage previous = m_strokePreviewLayerImage;
    m_strokePreviewLayerImage = layerImage;
    const QImage result = composeLayersRegion(QRect(QPoint(), m_documentSize));
    m_strokePreviewLayerImage = previous;
    return result;
}

bool DrawingCanvas::canUseGpuDirectStrokePreview() const
{
    if (m_activeLayerIndex != 0 || m_layers.size() != 1) return false;
    const RasterLayer &layer = m_layers.constFirst();
    return layer.type == QStringLiteral("raster") && layer.visible && !layer.locked
           && !layer.maskEnabled && !layer.transparentPixelsLocked && layer.textElements.isEmpty()
           && layer.blendMode == QStringLiteral("normal") && layer.opacityPercent == 100
           && !hasSelectionRegion();
}

void DrawingCanvas::endExternalUvStroke()
{
    m_suppressExternalStrokeDisplay = false;
    endStroke();
    m_externalUvStrokeActive = false;
    m_externalStrokeDisplayImage = QImage();
    m_projectedStampProvider = {};
    m_projectedSurfaceHitProvider = {};
    m_projectedWorldProjector = {};
    m_projectedSceneSpacingActive = false;
    m_projectedStrokeScale = 1.0;
    m_projectedSpacingScale = 1.0;
}

void DrawingCanvas::endActiveStrokeForNavigation()
{
    if (m_externalUvStrokeActive || m_projectedStampProvider) endExternalUvStroke();
    else endStroke();
    m_straightStrokeActive = false;
}

bool DrawingCanvas::sampleCompositedColorAtCanvasPoint(const QPointF &canvasPoint, QColor *outColor) const
{
    if (!outColor || m_documentSize.width() <= 0 || m_documentSize.height() <= 0) {
        return false;
    }

    const int x = qBound(0, static_cast<int>(std::lround(canvasPoint.x())), qMax(0, m_documentSize.width() - 1));
    const int y = qBound(0, static_cast<int>(std::lround(canvasPoint.y())), qMax(0, m_documentSize.height() - 1));

    const QImage composed = composeLayers();
    if (composed.isNull() || !composed.valid(x, y)) {
        return false;
    }

    const QRgb premul = composed.pixel(x, y);
    *outColor = QColor::fromRgba(qUnpremultiply(premul));
    return true;
}

bool DrawingCanvas::sampleActiveLayerColorAtCanvasPoint(const QPointF &canvasPoint, QColor *outColor) const
{
    if (!outColor) {
        return false;
    }

    const QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        return false;
    }

    const int x = qBound(0, static_cast<int>(std::lround(canvasPoint.x())), qMax(0, layerImage->width() - 1));
    const int y = qBound(0, static_cast<int>(std::lround(canvasPoint.y())), qMax(0, layerImage->height() - 1));
    if (!layerImage->valid(x, y)) {
        return false;
    }

    const QRgb premul = layerImage->pixel(x, y);
    *outColor = QColor::fromRgba(qUnpremultiply(premul));
    return true;
}

bool DrawingCanvas::sampleCompositedColorAtUv(const QPointF &uv, QColor *outColor) const
{
    const qreal u = qBound(0.0, uv.x(), 1.0);
    const qreal v = qBound(0.0, uv.y(), 1.0);
    const QPointF canvasPoint(
        u * qMax(1, m_documentSize.width() - 1),
        (1.0 - v) * qMax(1, m_documentSize.height() - 1));
    return sampleCompositedColorAtCanvasPoint(canvasPoint, outColor);
}

bool DrawingCanvas::sampleActiveLayerColorAtUv(const QPointF &uv, QColor *outColor) const
{
    const qreal u = qBound(0.0, uv.x(), 1.0);
    const qreal v = qBound(0.0, uv.y(), 1.0);
    const QPointF canvasPoint(
        u * qMax(1, m_documentSize.width() - 1),
        (1.0 - v) * qMax(1, m_documentSize.height() - 1));
    return sampleActiveLayerColorAtCanvasPoint(canvasPoint, outColor);
}

void DrawingCanvas::applyExternalUvStrokeBatch(const QVector<QPointF> &uvPoints,
                                               const QVector<qreal> &pressures,
                                               bool beginStrokeFlag,
                                               bool endStrokeFlag)
{
    if (uvPoints.isEmpty()) {
        if (endStrokeFlag) {
            endExternalUvStroke();
        }
        return;
    }

    const int count = qMin(uvPoints.size(), pressures.size());
    if (count <= 0) {
        return;
    }

    const int docWm1 = qMax(1, m_documentSize.width() - 1);
    const int docHm1 = qMax(1, m_documentSize.height() - 1);

    const auto uvToCanvas = [docWm1, docHm1](const QPointF &uv) {
        const qreal u = qBound(0.0, uv.x(), 1.0);
        const qreal v = qBound(0.0, uv.y(), 1.0);
        return QPointF(u * docWm1, (1.0 - v) * docHm1);
    };

    const auto beginAt = [this, &uvToCanvas](const QPointF &uv, qreal pressure) {
        m_externalStrokeDisplayImage = m_maskPaintingEnabled
                                        ? QImage()
                                        : ((!m_composedCache.isNull()
                                            && m_composedCacheRevision == m_contentRevision)
                                               ? m_composedCache
                                               : composeLayers());
        m_externalUvStrokeActive = true;
        m_suppressExternalStrokeDisplay = true;
        if (m_projectedStampProvider) {
            beginStroke(uv, qBound(0.05, pressure, 1.0));
            // A projected stroke used to initialise its GPU session here but
            // wait for a second pointer sample before submitting any dab.
            // Clicks and short first movements consequently produced an empty
            // stroke, then appeared to work only on the next attempt.
            continueExternalUvStroke(uv, qBound(0.05, pressure, 1.0));
            return;
        }
        m_externalUvIslandIndex = -1;
        updateExternalUvIsland(uvToCanvas(uv));
        beginStroke(uvToCanvas(uv), qBound(0.05, pressure, 1.0));
    };

    const auto continueAt = [this](const QPointF &uv, qreal pressure) {
        continueExternalUvStroke(uv, pressure);
    };

    ensureLayers();

    if (beginStrokeFlag || !m_isDrawing) {
        beginAt(uvPoints[0], pressures[0]);
        for (int i = 1; i < count; ++i) {
            continueAt(uvPoints[i], pressures[i]);
        }
    } else {
        for (int i = 0; i < count; ++i) {
            continueAt(uvPoints[i], pressures[i]);
        }
    }

    if (endStrokeFlag && m_isDrawing && !m_pendingProjectedSegment) {
        endExternalUvStroke();
    } else if (m_isDrawing && !m_projectedStampProvider) {
        // External 3D batches update the transient preview before the stroke
        // is committed. Advance the revision so the coalesced viewport sync
        // does not incorrectly treat the previous texture as up to date.
        bumpContentRevision();
    }

}

int DrawingCanvas::applyExternalUvStrokeBatchSlice(const QVector<QPointF> &points,
    const QVector<qreal> &pressures, bool beginStrokeFlag, bool endStrokeFlag, qint64 budgetMs)
{
    const int count = qMin(points.size(), pressures.size());
    if (budgetMs < 0 || count == 0) {
        applyExternalUvStrokeBatch(points, pressures, beginStrokeFlag, endStrokeFlag);
        return count;
    }
    m_projectedSliceTimer.start();
    m_projectedSliceBudget = budgetMs;
    int consumed = 0;
    do {
        applyExternalUvStrokeBatch({points[consumed]}, {pressures[consumed]},
            beginStrokeFlag && consumed == 0, endStrokeFlag && consumed + 1 == count);
        if (m_pendingProjectedSegment) break;
        ++consumed;
    } while (consumed < count && m_projectedSliceTimer.elapsed() < budgetMs);
    m_projectedSliceBudget = -1;
    return consumed;
}

void DrawingCanvas::applyExternalUvDabStroke(const QVector<QPointF> &uvPoints, qreal pressure)
{
    if (uvPoints.isEmpty()) return;
    ensureLayers();
    const qreal p = qBound(0.05, pressure, 1.0);
    const auto toCanvas = [this](const QPointF &uv) {
        return QPointF(qBound(0.0, uv.x(), 1.0) * qMax(1, m_documentSize.width() - 1),
                       (1.0 - qBound(0.0, uv.y(), 1.0)) * qMax(1, m_documentSize.height() - 1));
    };

    // A dab stroke is synchronous, but paintEvent can still run from drawDab().
    // Freeze the 2D view before changing the active layer, just like the
    // batched 3D-stroke path.
    m_externalStrokeDisplayImage = (!m_composedCache.isNull()
                                    && m_composedCacheRevision == m_contentRevision)
                                       ? m_composedCache
                                       : composeLayers();
    m_externalUvStrokeActive = true;
    m_suppressExternalStrokeDisplay = true;
    m_externalUvIslandIndex = -1;
    updateExternalUvIsland(toCanvas(uvPoints.front()));
    beginStroke(toCanvas(uvPoints.front()), p);
    for (int i = 1; i < uvPoints.size(); ++i) {
        const QPointF point = toCanvas(uvPoints[i]);
        updateExternalUvIsland(point);
        drawDab(point, p);
        m_lastPoint = point;
        m_lastPressure = p;
    }
    endStroke();
    m_externalUvStrokeActive = false;
    m_suppressExternalStrokeDisplay = false;
    m_externalStrokeDisplayImage = QImage();
    update();
}

void DrawingCanvas::setUvOverlay(const QVector<QPointF> &uvPoints, const QVector<quint32> &indices)
{
    m_uvOverlayPoints = uvPoints;
    m_uvOverlayIndices = indices;
    invalidateUvOverlaySnapshot();
    rebuildUvClipRegion();
    update();
}

void DrawingCanvas::setExternalUvFaceSelection(const QVector<QPointF> &uvPoints,
                                               const QVector<quint32> &indices,
                                               const QVector<int> &faceIndices)
{
    m_externalUvFaceClipRegion = QRegion();
    m_externalUvFaceSelectionActive = !faceIndices.isEmpty();
    if (faceIndices.isEmpty() || uvPoints.isEmpty() || indices.size() < 3) return;

    const qreal maxX = qMax(1, m_documentSize.width() - 1);
    const qreal maxY = qMax(1, m_documentSize.height() - 1);
    for (int face : faceIndices) {
        const int base = face * 3;
        if (face < 0 || base + 2 >= indices.size()) continue;
        const quint32 i0 = indices[base];
        const quint32 i1 = indices[base + 1];
        const quint32 i2 = indices[base + 2];
        if (i0 >= static_cast<quint32>(uvPoints.size())
            || i1 >= static_cast<quint32>(uvPoints.size())
            || i2 >= static_cast<quint32>(uvPoints.size())) continue;
        auto toCanvas = [maxX, maxY](const QPointF &uv) {
            return QPointF(qBound(0.0, uv.x(), 1.0) * maxX,
                           (1.0 - qBound(0.0, uv.y(), 1.0)) * maxY);
        };
        QPolygon polygon;
        polygon << toCanvas(uvPoints[static_cast<int>(i0)]).toPoint()
                << toCanvas(uvPoints[static_cast<int>(i1)]).toPoint()
                << toCanvas(uvPoints[static_cast<int>(i2)]).toPoint();
        m_externalUvFaceClipRegion = m_externalUvFaceClipRegion.united(QRegion(polygon, Qt::WindingFill));
    }
}

void DrawingCanvas::clearUvOverlay()
{
    m_uvOverlayPoints.clear();
    m_uvOverlayIndices.clear();
    invalidateUvOverlaySnapshot();
    m_uvClipRegion = QRegion();
    m_projectedUvInteriorRegion = QRegion();
    m_uvIslandRegions.clear();
    m_externalUvIslandClipRegion = QRegion();
    m_externalUvIslandIndex = -1;
    update();
}

void DrawingCanvas::setUvOverlayVisible(bool visible)
{
    m_uvOverlayVisible = visible;
    update();
}

bool DrawingCanvas::uvOverlayVisible() const
{
    return m_uvOverlayVisible;
}

void DrawingCanvas::setUvOverlayOpacityPercent(int opacityPercent)
{
    const int bounded = qBound(0, opacityPercent, 100);
    if (m_uvOverlayOpacityPercent == bounded) return;
    m_uvOverlayOpacityPercent = bounded;
    invalidateUvOverlaySnapshot();
    update();
}

int DrawingCanvas::uvOverlayOpacityPercent() const
{
    return m_uvOverlayOpacityPercent;
}

void DrawingCanvas::setUvOverlayColor(const QColor &color)
{
    if (!color.isValid() || m_uvOverlayColor == color) return;
    m_uvOverlayColor = color;
    invalidateUvOverlaySnapshot();
    update();
}

QColor DrawingCanvas::uvOverlayColor() const
{
    return m_uvOverlayColor;
}

void DrawingCanvas::invalidateUvOverlaySnapshot()
{
    ++m_uvOverlayRevision;
    if (m_uvOverlayRevision == 0) ++m_uvOverlayRevision;
}

const QImage &DrawingCanvas::uvOverlaySnapshot(const QSize &displaySize)
{
    const QSize size = displaySize.expandedTo(QSize());
    // UV topology is immutable between material/canvas changes. The periodic
    // check is intentionally cheap; data changes use the explicit invalidator.
    if (!m_uvOverlaySnapshotCheckTimer.isValid() || m_uvOverlaySnapshotCheckTimer.elapsed() >= 5000)
        m_uvOverlaySnapshotCheckTimer.restart();
    if (!m_uvOverlaySnapshot.isNull() && m_uvOverlaySnapshotSize == size
        && m_uvOverlaySnapshotRevision == m_uvOverlayRevision) {
        return m_uvOverlaySnapshot;
    }
    m_uvOverlaySnapshot = QImage(size, QImage::Format_ARGB32_Premultiplied);
    m_uvOverlaySnapshot.fill(Qt::transparent);
    m_uvOverlaySnapshotSize = size;
    m_uvOverlaySnapshotRevision = m_uvOverlayRevision;
    if (size.isEmpty() || m_uvOverlayPoints.isEmpty() || m_uvOverlayIndices.size() < 3)
        return m_uvOverlaySnapshot;

    QPainter snapshotPainter(&m_uvOverlaySnapshot);
    snapshotPainter.setRenderHint(QPainter::Antialiasing, true);
    QColor color = m_uvOverlayColor;
    color.setAlpha(qRound(220.0 * m_uvOverlayOpacityPercent / 100.0));
    snapshotPainter.setPen(QPen(color, 1.0));
    const auto pointAt = [&size](const QPointF &uv) {
        return QPointF(qBound(0.0, uv.x(), 1.0) * qMax(1, size.width() - 1),
                       (1.0 - qBound(0.0, uv.y(), 1.0)) * qMax(1, size.height() - 1));
    };
    const int triCount = m_uvOverlayIndices.size() / 3;
    for (int t = 0; t < triCount; ++t) {
        const quint32 i0 = m_uvOverlayIndices[t * 3 + 0];
        const quint32 i1 = m_uvOverlayIndices[t * 3 + 1];
        const quint32 i2 = m_uvOverlayIndices[t * 3 + 2];
        if (i0 >= static_cast<quint32>(m_uvOverlayPoints.size())
            || i1 >= static_cast<quint32>(m_uvOverlayPoints.size())
            || i2 >= static_cast<quint32>(m_uvOverlayPoints.size())) continue;
        const QPointF p0 = pointAt(m_uvOverlayPoints.at(static_cast<int>(i0)));
        const QPointF p1 = pointAt(m_uvOverlayPoints.at(static_cast<int>(i1)));
        const QPointF p2 = pointAt(m_uvOverlayPoints.at(static_cast<int>(i2)));
        snapshotPainter.drawLine(p0, p1);
        snapshotPainter.drawLine(p1, p2);
        snapshotPainter.drawLine(p2, p0);
    }
    return m_uvOverlaySnapshot;
}

void DrawingCanvas::setCanvasMargin(int margin)
{
    const int clamped = qBound(0, margin, 20000);
    if (m_canvasMargin == clamped) {
        return;
    }
    m_canvasMargin = clamped;
    update();
}

int DrawingCanvas::canvasMargin() const
{
    return m_canvasMargin;
}

qreal DrawingCanvas::snappedRotationDegrees(qreal degrees) const
{
    if (!m_rotationSnapEnabled) {
        return degrees;
    }
    return std::round(degrees / 5.0) * 5.0;
}

void DrawingCanvas::setViewRotationDegrees(qreal degrees)
{
    const qreal normalized = std::fmod(snappedRotationDegrees(degrees), 360.0);
    const qreal wrapped = (normalized < 0.0) ? (normalized + 360.0) : normalized;
    if (std::abs(m_viewRotationDegrees - wrapped) < 0.0001) {
        return;
    }
    m_viewRotationDegrees = wrapped;
    update();
}

qreal DrawingCanvas::viewRotationDegrees() const
{
    return m_viewRotationDegrees;
}

void DrawingCanvas::setRotationSnapEnabled(bool enabled)
{
    if (m_rotationSnapEnabled == enabled) {
        return;
    }
    m_rotationSnapEnabled = enabled;
}

bool DrawingCanvas::rotationSnapEnabled() const
{
    return m_rotationSnapEnabled;
}

void DrawingCanvas::setQuickAdjustEnabled(bool enabled)
{
    if (m_quickAdjustEnabled == enabled) {
        return;
    }
    m_quickAdjustEnabled = enabled;
    if (!m_quickAdjustEnabled && m_quickAdjustMode != QuickAdjustMode::None) {
        cancelQuickAdjust();
    }
}

QRectF DrawingCanvas::rotatedArtBoundingRectInWidget() const
{
    const QRect artRect = canvasRect();
    QRectF bounds(artRect);
    if (std::abs(m_viewRotationDegrees) < 0.0001) {
        return bounds;
    }

    const QPointF center = bounds.center();
    const QPointF p0 = rotatePointAround(bounds.topLeft(), center, m_viewRotationDegrees);
    const QPointF p1 = rotatePointAround(bounds.topRight(), center, m_viewRotationDegrees);
    const QPointF p2 = rotatePointAround(bounds.bottomLeft(), center, m_viewRotationDegrees);
    const QPointF p3 = rotatePointAround(bounds.bottomRight(), center, m_viewRotationDegrees);

    const qreal minX = qMin(qMin(p0.x(), p1.x()), qMin(p2.x(), p3.x()));
    const qreal maxX = qMax(qMax(p0.x(), p1.x()), qMax(p2.x(), p3.x()));
    const qreal minY = qMin(qMin(p0.y(), p1.y()), qMin(p2.y(), p3.y()));
    const qreal maxY = qMax(qMax(p0.y(), p1.y()), qMax(p2.y(), p3.y()));

    return QRectF(QPointF(minX, minY), QPointF(maxX, maxY));
}

QPointF DrawingCanvas::viewRotationPivotInWidget() const
{
    return canvasRect().center();
}

void DrawingCanvas::setBrushSize(int size)
{
    const int clamped = qBound(1, size, 1000);
    if (m_baseBrushSize == clamped) {
        return;
    }
    m_baseBrushSize = clamped;
    update();
    if (onBrushSizeChanged) {
        onBrushSizeChanged(m_baseBrushSize);
    }
}

void DrawingCanvas::setHardness(int hardnessPercent)
{
    m_hardnessPercent = qBound(1, hardnessPercent, 100);
}

void DrawingCanvas::setSpacing(int spacingPercent)
{
    m_spacingPercent = qBound(10, spacingPercent, 150);
}

void DrawingCanvas::setOpacity(int opacityPercent)
{
    const int clamped = qBound(1, opacityPercent, 100);
    if (m_opacityPercent == clamped) {
        return;
    }
    m_opacityPercent = clamped;
    if (onBrushOpacityChanged) {
        onBrushOpacityChanged(m_opacityPercent);
    }
}

void DrawingCanvas::setFlow(int flowPercent)
{
    Q_UNUSED(flowPercent);
    m_flowPercent = 100;
}

void DrawingCanvas::setRoundness(int roundnessPercent)
{
    m_roundnessPercent = qBound(1, roundnessPercent, 100);
}

void DrawingCanvas::setAngle(int angleDegrees)
{
    m_angleDegrees = ((angleDegrees % 360) + 360) % 360;
}

void DrawingCanvas::setRandomAngle(int angleDegrees)
{
    m_randomAngleDegrees = qBound(0, angleDegrees, 180);
}

void DrawingCanvas::setBrushTipCircle()
{
    if (!m_useTextureTip) {
        return;
    }
    m_useTextureTip = false;
    m_brushStampCache.clear();
    m_brushStampMaxAlphaCache.clear();
    update();
}

void DrawingCanvas::setBrushTipTexture(const QImage &textureImage)
{
    if (textureImage.isNull()) {
        setBrushTipCircle();
        return;
    }

    QImage normalized = textureImage.convertToFormat(QImage::Format_ARGB32_Premultiplied);
    if (normalized.width() > 512 || normalized.height() > 512) {
        normalized = normalized.scaled(512, 512, Qt::KeepAspectRatio, Qt::SmoothTransformation);
    }

    m_tipTextureImage = normalized;
    m_useTextureTip = true;
    ++m_tipTextureToken;
    if (m_tipTextureToken == 0) {
        m_tipTextureToken = 1;
    }
    m_brushStampCache.clear();
    m_brushStampMaxAlphaCache.clear();
    update();
}

void DrawingCanvas::setSprayEnabled(bool enabled)
{
    m_sprayEnabled = enabled;
}

void DrawingCanvas::setSprayRangePercent(int percent)
{
    m_sprayRangePercent = qBound(10, percent, 300);
}

void DrawingCanvas::setSprayDensity(int density)
{
    m_sprayDensity = qBound(1, density, 64);
}

void DrawingCanvas::setSprayCenterDensity(int percent)
{
    m_sprayCenterDensityPercent = qBound(0, percent, 100);
}

void DrawingCanvas::setSprayParticleSize(int pixels)
{
    m_sprayParticleSizePixels = qBound(1, pixels, 128);
}

void DrawingCanvas::setSprayParticleRandomSize(int percent)
{
    m_sprayParticleRandomSizePercent = qBound(0, percent, 100);
}

void DrawingCanvas::setSprayParticleRotation(int degrees)
{
    m_sprayParticleRotationDegrees = qBound(0, degrees, 360);
}

void DrawingCanvas::setSprayParticleRandomRotation(int degrees)
{
    m_sprayParticleRandomRotationDegrees = qBound(0, degrees, 180);
}

void DrawingCanvas::setPressureSizeEnabled(bool enabled)
{
    m_pressureSizeEnabled = enabled;
}

void DrawingCanvas::setPressureOpacityEnabled(bool enabled)
{
    m_pressureOpacityEnabled = enabled;
}

void DrawingCanvas::setPressureSizeMinPercent(int percent)
{
    m_pressureSizeMinPercent = qBound(0, percent, 100);
}

void DrawingCanvas::setPressureOpacityMinPercent(int percent)
{
    m_pressureOpacityMinPercent = qBound(0, percent, 100);
}

void DrawingCanvas::setPressureSizeCurve(const QVector<qreal> &curve)
{
    if (curve.size() < 2) {
        return;
    }
    m_pressureSizeCurve = curve;
    for (qreal &v : m_pressureSizeCurve) {
        v = qBound(0.0, v, 1.0);
    }
}

void DrawingCanvas::setPressureOpacityCurve(const QVector<qreal> &curve)
{
    if (curve.size() < 2) {
        return;
    }
    m_pressureOpacityCurve = curve;
    for (qreal &v : m_pressureOpacityCurve) {
        v = qBound(0.0, v, 1.0);
    }
}
qreal DrawingCanvas::brushPreviewRadiusPx(qreal pressure) const
{
    const qreal sizeFactor = sizePressureFactor(pressure);
    return qMax(0.5, (m_baseBrushSize * sizeFactor) * 0.5);
}

int DrawingCanvas::brushSize() const
{
    return m_baseBrushSize;
}

qreal DrawingCanvas::projectedBrushScreenScale(const QSize &viewportSize) const
{
    if (m_projectedStampProvider) return m_projectedStrokeScale;
    return qBound(0.15, qMin(qreal(qMax(1, viewportSize.width())) / qMax(1, m_documentSize.width()),
                            qreal(qMax(1, viewportSize.height())) / qMax(1, m_documentSize.height())), 1.0);
}

QPainterPath DrawingCanvas::projectedBrushCursorPath(qreal pressure, const QSize &viewportSize, int previewSize) const
{
    const qreal radiusX = previewSize > 0
        ? qMax(0.5, qBound(1, previewSize, 1000) * sizePressureFactor(pressure) * 0.5)
        : brushPreviewRadiusPx(pressure);
    const qreal radiusY = qMax(0.5, radiusX * (m_roundnessPercent / 100.0));
    const qreal stampRadiusX = qMax(1.0, std::ceil(radiusX));
    const qreal stampRadiusY = qMax(1.0, std::ceil(radiusY));
    QPainterPath outline;
    outline.addEllipse(QRectF(-stampRadiusX, -stampRadiusY, stampRadiusX * 2.0, stampRadiusY * 2.0));
    QTransform transform;
    transform.rotate(m_angleDegrees);
    const qreal scale = projectedBrushScreenScale(viewportSize);
    transform.scale(scale, scale);
    return transform.map(outline);
}

int DrawingCanvas::brushOpacityPercent() const
{
    return m_opacityPercent;
}

quint64 DrawingCanvas::contentRevision() const
{
    return m_contentRevision;
}

void DrawingCanvas::setCanvasBackgroundColor(const QColor &color)
{
    m_canvasBackgroundColor = color;
    update();
}

void DrawingCanvas::setBrushInkColor(const QColor &color)
{
    if (!color.isValid()) return;
    m_brushInkColor = m_grayscaleOnly
        ? QColor(qGray(color.rgb()), qGray(color.rgb()), qGray(color.rgb()), color.alpha())
        : color;
}

void DrawingCanvas::setGrayscaleOnly(bool enabled)
{
    if (m_grayscaleOnly == enabled) return;
    m_grayscaleOnly = enabled;
    if (!m_grayscaleOnly) return;
    for (RasterLayer &layer : m_layers) {
        if (!layer.image.isNull()) {
            layer.image = grayscaleImagePreservingAlpha(layer.image);
        }
    }
    m_brushInkColor = QColor(qGray(m_brushInkColor.rgb()), qGray(m_brushInkColor.rgb()),
                             qGray(m_brushInkColor.rgb()), m_brushInkColor.alpha());
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
}

void DrawingCanvas::applyProjectedGradientToUvFaces(int index,
                                                     const QVector<QPointF> &uvPoints,
                                                     const QVector<QPointF> &projectedPoints,
                                                     const QVector<quint32> &indices,
                                                     const QVector<int> &triangleIndices,
                                                     const QPointF &startScreen,
                                                     const QPointF &endScreen,
                                                     const QColor &startColor,
                                                     const QColor &endColor)
{
    if (index < 0 || index >= m_layers.size() || triangleIndices.isEmpty()
        || uvPoints.size() != projectedPoints.size() || !startColor.isValid() || !endColor.isValid()) return;
    RasterLayer &layer = m_layers[index];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) return;

    const QPointF axis = endScreen - startScreen;
    const qreal axisLength2 = QPointF::dotProduct(axis, axis);
    if (axisLength2 < 1e-5) return;
    const int maxX = qMax(0, targetImage->width() - 1);
    const int maxY = qMax(0, targetImage->height() - 1);
    const auto uvToPixel = [maxX, maxY](const QPointF &uv) {
        return QPointF(qBound(0.0, uv.x(), 1.0) * (maxX + 1),
                       (1.0 - qBound(0.0, uv.y(), 1.0)) * (maxY + 1));
    };
    const auto blend = [&](qreal t) {
        t = qBound(0.0, t, 1.0);
        const QColor color = QColor::fromRgbF(startColor.redF() + (endColor.redF() - startColor.redF()) * t,
                                               startColor.greenF() + (endColor.greenF() - startColor.greenF()) * t,
                                               startColor.blueF() + (endColor.blueF() - startColor.blueF()) * t,
                                               startColor.alphaF() + (endColor.alphaF() - startColor.alphaF()) * t);
        const int gray = qGray(color.rgb());
        return editingMask ? QColor(gray, gray, gray) : color;
    };

    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (!editingMask) pushUndoHistoryState();
    QImage workingMask;
    QImage *image = &layer.image;
    if (editingMask) {
        workingMask = targetImage->convertToFormat(QImage::Format_ARGB32_Premultiplied);
        image = &workingMask;
    }
    for (int tri : triangleIndices) {
        const int base = tri * 3;
        if (tri < 0 || base + 2 >= indices.size()) continue;
        const int i0 = static_cast<int>(indices[base]);
        const int i1 = static_cast<int>(indices[base + 1]);
        const int i2 = static_cast<int>(indices[base + 2]);
        if (i0 < 0 || i1 < 0 || i2 < 0 || i0 >= uvPoints.size() || i1 >= uvPoints.size() || i2 >= uvPoints.size()) continue;
        if (!std::isfinite(projectedPoints[i0].x()) || !std::isfinite(projectedPoints[i0].y())
            || !std::isfinite(projectedPoints[i1].x()) || !std::isfinite(projectedPoints[i1].y())
            || !std::isfinite(projectedPoints[i2].x()) || !std::isfinite(projectedPoints[i2].y())) {
            continue;
        }
        QPointF a = uvToPixel(uvPoints[i0]);
        QPointF b = uvToPixel(uvPoints[i1]);
        QPointF c = uvToPixel(uvPoints[i2]);
        const qreal denom = (b.y() - c.y()) * (a.x() - c.x()) + (c.x() - b.x()) * (a.y() - c.y());
        if (qAbs(denom) < 1e-7) continue;
        const int left = qBound(0, static_cast<int>(std::floor(qMin(a.x(), qMin(b.x(), c.x())))) - 1, maxX);
        const int right = qBound(0, static_cast<int>(std::ceil(qMax(a.x(), qMax(b.x(), c.x())))) + 1, maxX);
        const int top = qBound(0, static_cast<int>(std::floor(qMin(a.y(), qMin(b.y(), c.y())))) - 1, maxY);
        const int bottom = qBound(0, static_cast<int>(std::ceil(qMax(a.y(), qMax(b.y(), c.y())))) + 1, maxY);
        const auto edgeDistanceSquared = [](const QPointF &point, const QPointF &start, const QPointF &end) {
            const QPointF edge = end - start;
            const qreal lengthSquared = QPointF::dotProduct(edge, edge);
            const qreal amount = lengthSquared > 0.0
                ? qBound(0.0, QPointF::dotProduct(point - start, edge) / lengthSquared, 1.0) : 0.0;
            const QPointF offset = point - (start + edge * amount);
            return QPointF::dotProduct(offset, offset);
        };
        for (int y = top; y <= bottom; ++y) {
            QRgb *row = reinterpret_cast<QRgb *>(image->scanLine(y));
            for (int x = left; x <= right; ++x) {
                const QPointF p(x + 0.5, y + 0.5);
                const qreal w0 = ((b.y() - c.y()) * (p.x() - c.x()) + (c.x() - b.x()) * (p.y() - c.y())) / denom;
                const qreal w1 = ((c.y() - a.y()) * (p.x() - c.x()) + (a.x() - c.x()) * (p.y() - c.y())) / denom;
                const qreal w2 = 1.0 - w0 - w1;
                if ((w0 < -0.0001 || w1 < -0.0001 || w2 < -0.0001)
                    && edgeDistanceSquared(p, a, b) > 1.0
                    && edgeDistanceSquared(p, b, c) > 1.0
                    && edgeDistanceSquared(p, c, a) > 1.0) continue;
                const QPointF screen = projectedPoints[i0] * w0 + projectedPoints[i1] * w1 + projectedPoints[i2] * w2;
                const qreal t = QPointF::dotProduct(screen - startScreen, axis) / axisLength2;
                row[x] = qPremultiply(blend(t).rgba());
            }
        }
    }
    if (editingMask) {
        layer.maskImage = workingMask.convertToFormat(QImage::Format_Grayscale8);
        layer.meshMaskFaceIndices.clear();
    }
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
}

void DrawingCanvas::setBrushTipAntiAliasingEnabled(bool enabled)
{
    if (m_tipAntiAliasingEnabled == enabled) {
        return;
    }
    m_tipAntiAliasingEnabled = enabled;
    m_brushStampCache.clear();
    m_brushStampMaxAlphaCache.clear();
    update();
}

bool DrawingCanvas::grayscaleOnly() const
{
    return m_grayscaleOnly;
}

void DrawingCanvas::setOutlineColors(const QColor &outer, const QColor &inner, const QColor &shadow)
{
    if (outer.isValid()) {
        m_outlineOuterColor = outer;
    }
    if (inner.isValid()) {
        m_outlineInnerColor = inner;
    }
    if (shadow.isValid()) {
        m_outlineShadowColor = shadow;
    }
    update();
}

void DrawingCanvas::setSymmetryGuideColor(const QColor &color)
{
    if (!color.isValid()) {
        return;
    }
    if (m_symmetryGuideColor == color) {
        return;
    }
    m_symmetryGuideColor = color;
    update();
}

QColor DrawingCanvas::symmetryGuideColor() const
{
    return m_symmetryGuideColor;
}

void DrawingCanvas::emitSymmetrySettingsChanged()
{
    if (onSymmetrySettingsChanged) {
        onSymmetrySettingsChanged();
    }
}

QPointF DrawingCanvas::symmetryCenterCanvasPoint() const
{
    const QPointF baseCenter((qMax(1, m_documentSize.width()) - 1) * 0.5,
                             (qMax(1, m_documentSize.height()) - 1) * 0.5);
    return baseCenter + m_symmetryCenterOffsetCanvas;
}

QPointF DrawingCanvas::symmetryRotationHandleCanvasPoint() const
{
    const QPointF center = symmetryCenterCanvasPoint();
    const qreal radius = qMax(40.0,
                              qMin(m_documentSize.width(), m_documentSize.height())
                                  * 0.24);
    const qreal radians = m_symmetryRotationDegrees * 3.14159265358979323846 / 180.0;
    return center + QPointF(std::cos(radians) * radius, std::sin(radians) * radius);
}

QVector<QPointF> DrawingCanvas::symmetryStampPoints(const QPointF &point) const
{
    QVector<QPointF> points;
    if (!m_symmetryEnabled) {
        points.push_back(point);
        return points;
    }

    int segments = qBound(2, m_symmetrySegments, 8);
    if ((segments % 2) != 0) {
        segments = qMin(8, segments + 1);
    }
    const int axisCount = qMax(1, segments / 2);

    const QPointF center = m_projectedStampProvider
        ? m_projectedSymmetryCenter + m_symmetryCenterOffsetCanvas * m_projectedStrokeScale
        : symmetryCenterCanvasPoint();
    const QPointF baseVector = point - center;
    const qreal baseRadians = m_symmetryRotationDegrees * 3.14159265358979323846 / 180.0;
    const qreal baseSin = std::sin(baseRadians);
    const qreal baseCos = std::cos(baseRadians);

    // Transform to the symmetry-local frame so the first stamp always stays
    // on the cursor position while the remaining stamps follow the selected
    // mirror or rotational symmetry mode.
    const QPointF local(baseCos * baseVector.x() + baseSin * baseVector.y(),
                        -baseSin * baseVector.x() + baseCos * baseVector.y());

    points.reserve(segments);
    const int rotationCount = m_symmetryMirrorMode ? axisCount : segments;
    const qreal rotationStep = 360.0 / static_cast<qreal>(rotationCount);
    const auto appendUniqueLocal = [&](const QPointF &candidateLocal) {
        const QPointF worldVector(baseCos * candidateLocal.x() - baseSin * candidateLocal.y(),
                                  baseSin * candidateLocal.x() + baseCos * candidateLocal.y());
        const QPointF transformed = center + worldVector;
        // Avoid a square-root per comparison: this runs for every symmetry
        // copy of every brush stamp, including high-rate tablet packets.
        constexpr qreal kDuplicateDistanceSquared = 0.0001;
        for (const QPointF &existing : std::as_const(points)) {
            const QPointF delta = existing - transformed;
            if (QPointF::dotProduct(delta, delta) <= kDuplicateDistanceSquared) {
                return;
            }
        }
        points.push_back(transformed);
    };
    for (int axisIndex = 0; axisIndex < rotationCount; ++axisIndex) {
        const qreal radians = rotationStep * axisIndex * 3.14159265358979323846 / 180.0;
        const qreal s = std::sin(radians);
        const qreal c = std::cos(radians);

        const QPointF rotatedLocal(local.x() * c - local.y() * s,
                                   local.x() * s + local.y() * c);
        appendUniqueLocal(rotatedLocal);
        if (m_symmetryMirrorMode) {
            appendUniqueLocal(QPointF(rotatedLocal.x(), -rotatedLocal.y()));
        }
    }

    if (points.isEmpty()) {
        points.push_back(point);
    }
    return points;
}

void DrawingCanvas::setSymmetryEnabled(bool enabled)
{
    if (m_symmetryEnabled == enabled) {
        return;
    }

    m_symmetryEnabled = enabled;
    if (!m_symmetryEnabled) {
        endSymmetryHandleDrag();
    }
    emitSymmetrySettingsChanged();
    update();
}

bool DrawingCanvas::symmetryEnabled() const
{
    return m_symmetryEnabled;
}

void DrawingCanvas::setSymmetryMirrorMode(bool enabled)
{
    if (m_symmetryMirrorMode == enabled) {
        return;
    }
    m_symmetryMirrorMode = enabled;
    emitSymmetrySettingsChanged();
    update();
}

bool DrawingCanvas::symmetryMirrorMode() const
{
    return m_symmetryMirrorMode;
}

void DrawingCanvas::setSymmetryTransformLocked(bool locked)
{
    if (m_symmetryTransformLocked == locked) {
        return;
    }
    m_symmetryTransformLocked = locked;
    if (locked) {
        endSymmetryHandleDrag();
    }
    emitSymmetrySettingsChanged();
    update();
}

bool DrawingCanvas::symmetryTransformLocked() const
{
    return m_symmetryTransformLocked;
}

void DrawingCanvas::setSymmetrySegments(int segments)
{
    int clamped = qBound(2, segments, 8);
    if ((clamped % 2) != 0) {
        clamped = qMin(8, clamped + 1);
    }
    if (m_symmetrySegments == clamped) {
        return;
    }

    m_symmetrySegments = clamped;
    emitSymmetrySettingsChanged();
    update();
}

int DrawingCanvas::symmetrySegments() const
{
    return m_symmetrySegments;
}

void DrawingCanvas::setSymmetryRotationDegrees(qreal degrees)
{
    qreal wrapped = std::fmod(snappedRotationDegrees(degrees), 360.0);
    if (wrapped < 0.0) {
        wrapped += 360.0;
    }
    if (std::abs(m_symmetryRotationDegrees - wrapped) < 0.0001) {
        return;
    }

    m_symmetryRotationDegrees = wrapped;
    emitSymmetrySettingsChanged();
    update();
}

qreal DrawingCanvas::symmetryRotationDegrees() const
{
    return m_symmetryRotationDegrees;
}

void DrawingCanvas::setSymmetryCenterOffset(const QPointF &offsetCanvas)
{
    if (QLineF(m_symmetryCenterOffsetCanvas, offsetCanvas).length() < 0.0001) {
        return;
    }

    m_symmetryCenterOffsetCanvas = offsetCanvas;
    emitSymmetrySettingsChanged();
    update();
}

QPointF DrawingCanvas::symmetryCenterOffset() const
{
    return m_symmetryCenterOffsetCanvas;
}

DrawingCanvas::SymmetryHandleDragMode DrawingCanvas::symmetryHandleAtCanvasPoint(const QPointF &canvasPoint) const
{
    if (!m_symmetryEnabled || m_symmetryTransformLocked) {
        return SymmetryHandleDragMode::None;
    }

    const QPointF rotateHandle = symmetryRotationHandleCanvasPoint();
    if (QLineF(canvasPoint, rotateHandle).length() <= 12.0) {
        return SymmetryHandleDragMode::Rotate;
    }

    const QPointF center = symmetryCenterCanvasPoint();
    if (QLineF(canvasPoint, center).length() <= 12.0) {
        return SymmetryHandleDragMode::Move;
    }

    return SymmetryHandleDragMode::None;
}

bool DrawingCanvas::updateSymmetryHandleCursor(const QPointF &widgetPoint)
{
    if (m_selectionToolEnabled || !canvasRect().contains(widgetPoint.toPoint())) {
        return false;
    }

    SymmetryHandleDragMode mode = m_symmetryHandleDragMode;
    if (mode == SymmetryHandleDragMode::None) {
        mode = symmetryHandleAtCanvasPoint(widgetToCanvasPoint(widgetPoint));
    }
    if (mode == SymmetryHandleDragMode::None) {
        return false;
    }

    forceHideBrushCursor();
    setCursor(mode == SymmetryHandleDragMode::Move
                  ? QCursor(Qt::SizeAllCursor)
                  : freeTransformRotateCursor());
    return true;
}

void DrawingCanvas::beginSymmetryHandleDrag(SymmetryHandleDragMode mode, const QPointF &canvasPoint)
{
    if (!m_symmetryEnabled || m_symmetryTransformLocked || mode == SymmetryHandleDragMode::None) {
        return;
    }

    m_symmetryHandleDragMode = mode;
    m_symmetryDragStartCanvasPoint = canvasPoint;
    m_symmetryDragStartOffsetCanvas = m_symmetryCenterOffsetCanvas;
    m_symmetryDragStartRotationDegrees = m_symmetryRotationDegrees;
    m_symmetryDragAccumulatedDeltaDegrees = 0.0;
    m_symmetryHasDragLastCursorAngle = false;
    if (mode == SymmetryHandleDragMode::Rotate) {
        const QPointF center = symmetryCenterCanvasPoint();
        const QPointF v = canvasPoint - center;
        if (std::hypot(v.x(), v.y()) >= 0.001) {
            m_symmetryDragLastCursorAngleDegrees = std::atan2(v.y(), v.x()) * 180.0 / 3.14159265358979323846;
            m_symmetryHasDragLastCursorAngle = true;
        }
    }
    forceHideBrushCursor();
    update();
}

void DrawingCanvas::updateSymmetryHandleDrag(const QPointF &canvasPoint)
{
    if (m_symmetryHandleDragMode == SymmetryHandleDragMode::None) {
        return;
    }

    if (m_symmetryHandleDragMode == SymmetryHandleDragMode::Move) {
        const QPointF nextOffset = m_symmetryDragStartOffsetCanvas + (canvasPoint - m_symmetryDragStartCanvasPoint);
        if (QLineF(nextOffset, m_symmetryCenterOffsetCanvas).length() < 0.001) {
            return;
        }
        m_symmetryCenterOffsetCanvas = nextOffset;
        emitSymmetrySettingsChanged();
        update();
        return;
    }

    const QPointF center = symmetryCenterCanvasPoint();
    const QPointF currentVec = canvasPoint - center;
    if (std::hypot(currentVec.x(), currentVec.y()) < 0.001) {
        return;
    }

    qreal currentAngle = std::atan2(currentVec.y(), currentVec.x()) * 180.0 / 3.14159265358979323846;
    if (!m_symmetryHasDragLastCursorAngle) {
        m_symmetryDragLastCursorAngleDegrees = currentAngle;
        m_symmetryHasDragLastCursorAngle = true;
        return;
    }

    qreal delta = currentAngle - m_symmetryDragLastCursorAngleDegrees;
    while (delta > 180.0) {
        delta -= 360.0;
    }
    while (delta < -180.0) {
        delta += 360.0;
    }
    m_symmetryDragAccumulatedDeltaDegrees += delta;
    m_symmetryDragLastCursorAngleDegrees = currentAngle;

    qreal next = std::fmod(snappedRotationDegrees(m_symmetryDragStartRotationDegrees + m_symmetryDragAccumulatedDeltaDegrees), 360.0);
    if (next < 0.0) {
        next += 360.0;
    }

    if (std::abs(next - m_symmetryRotationDegrees) < 0.0001) {
        return;
    }

    m_symmetryRotationDegrees = next;
    emitSymmetrySettingsChanged();
    update();
}

void DrawingCanvas::endSymmetryHandleDrag()
{
    if (m_symmetryHandleDragMode == SymmetryHandleDragMode::None) {
        return;
    }
    m_symmetryHandleDragMode = SymmetryHandleDragMode::None;
    m_symmetryHasDragLastCursorAngle = false;
    m_symmetryDragAccumulatedDeltaDegrees = 0.0;
    update();
}

void DrawingCanvas::setMaskEditPreviewEnabled(bool enabled)
{
    if (m_maskEditPreviewEnabled == enabled) {
        return;
    }
    m_maskEditPreviewEnabled = enabled;
    update();
}

void DrawingCanvas::setSelectionToolEnabled(bool enabled)
{
    if (m_selectionToolEnabled == enabled) {
        return;
    }
    if (!enabled) {
        endFreeTransformInteraction(true);
        resetFreeTransformSession();
    }
    m_selectionToolEnabled = enabled;
    endSymmetryHandleDrag();
    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    if (enabled) {
        updateColorPickerPreviewFromWidgetPoint(QPointF(), Qt::NoModifier, false);
    }
    if (enabled) {
        forceHideBrushCursor();
        if (isFreeTransformMode()) {
            refreshFreeTransformSession();
        }
    }
    update();
}

bool DrawingCanvas::isSelectionToolEnabled() const
{
    return m_selectionToolEnabled;
}

void DrawingCanvas::setSelectionToolMode(const QString &mode)
{
    const QString normalized = mode.trimmed().toLower();
    const QString next = (normalized == QStringLiteral("rect")
                          || normalized == QStringLiteral("polyline")
                          || normalized == QStringLiteral("free_transform"))
                             ? normalized
                             : QStringLiteral("lasso");
    if (m_selectionToolMode == next) {
        return;
    }

    if (next == QStringLiteral("free_transform") && !isFreeTransformMode()) {
        m_selectionToolModeBeforeFreeTransform = m_selectionToolMode;
    }

    endFreeTransformInteraction(true);
    resetFreeTransformSession();

    m_selectionToolMode = next;
    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    if (isFreeTransformMode() && m_selectionToolEnabled) {
        ensureSelectionForFreeTransform();
        refreshFreeTransformSession();
    }
    update();
}

bool DrawingCanvas::ensureSelectionForFreeTransform()
{
    if (hasSelectionRegion()) {
        return true;
    }
    if (!isFreeTransformMode()) {
        return false;
    }
    if (!canMoveSelectionPixels()) {
        return false;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        return false;
    }

    QRegion region;
    const int w = layerImage->width();
    const int h = layerImage->height();
    for (int y = 0; y < h; ++y) {
        const QRgb *row = reinterpret_cast<const QRgb *>(layerImage->constScanLine(y));
        int runStart = -1;
        for (int x = 0; x < w; ++x) {
            const bool opaque = qAlpha(row[x]) > 0;
            if (opaque && runStart < 0) {
                runStart = x;
            } else if (!opaque && runStart >= 0) {
                region = region.united(QRegion(QRect(runStart, y, x - runStart, 1)));
                runStart = -1;
            }
        }
        if (runStart >= 0) {
            region = region.united(QRegion(QRect(runStart, y, w - runStart, 1)));
        }
    }

    if (region.isEmpty()) {
        return false;
    }

    setSelectionRegionInternal(region, false);
    if (m_hasSelectionRegion) {
        QPainterPath path;
        for (const QRect &rect : m_selectionClipRegion) {
            path.addRect(rect);
        }
        path = path.simplified();
        path.setFillRule(Qt::WindingFill);
        m_selectionPathCanvas = path;
        update();
        return true;
    }
    return false;
}

QString DrawingCanvas::selectionToolMode() const
{
    return m_selectionToolMode;
}

void DrawingCanvas::finalizeFreeTransform(bool accept)
{
    if (!isFreeTransformMode()) {
        return;
    }

    if (accept) {
        if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
            endFreeTransformInteraction(true);
        }
    } else {
        cancelFreeTransformSession();
    }

    resetFreeTransformSession();

    const QString previousMode = m_selectionToolModeBeforeFreeTransform.isEmpty()
                                     ? QStringLiteral("lasso")
                                     : m_selectionToolModeBeforeFreeTransform;
    setSelectionToolMode(previousMode);
}

QRectF DrawingCanvas::freeTransformBoundsInWidget() const
{
    if (!m_freeTransformSessionActive) {
        return QRectF();
    }

    QPainterPath boxPath;
    boxPath.addRect(m_freeTransformBaseBounds);
    const QPainterPath transformedView = freeTransformMatrix().map(boxPath);
    const QPainterPath transformedCanvas = viewAlignedToCanvasPath(transformedView);
    if (transformedCanvas.isEmpty() || transformedCanvas.elementCount() <= 0) {
        return QRectF();
    }

    qreal minX = std::numeric_limits<qreal>::max();
    qreal minY = std::numeric_limits<qreal>::max();
    qreal maxX = std::numeric_limits<qreal>::lowest();
    qreal maxY = std::numeric_limits<qreal>::lowest();

    for (int i = 0; i < transformedCanvas.elementCount(); ++i) {
        const QPainterPath::Element e = transformedCanvas.elementAt(i);
        const QPointF wp = canvasToWidgetPoint(QPointF(e.x, e.y));
        minX = qMin(minX, wp.x());
        minY = qMin(minY, wp.y());
        maxX = qMax(maxX, wp.x());
        maxY = qMax(maxY, wp.y());
    }

    if (minX > maxX || minY > maxY) {
        return QRectF();
    }

    return QRectF(QPointF(minX, minY), QPointF(maxX, maxY)).normalized();
}

void DrawingCanvas::clearSelectionRegion()
{
    if (m_selectionToolEnabled && isFreeTransformMode()) {
        return;
    }

    const bool wasSelected = hasSelectionRegion();
    endFreeTransformInteraction(false);
    resetFreeTransformSession();
    endSelectionTranslation(false);
    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    m_selectionPathCanvas = QPainterPath();
    m_selectionClipRegion = QRegion();
    m_hasSelectionRegion = false;
    updateSelectionAntsAnimationState();
    if (wasSelected && onSelectionRegionChanged) {
        onSelectionRegionChanged(false);
    }
    update();
}

void DrawingCanvas::clearSelectionRegionWithHistory()
{
    if (m_selectionToolEnabled && isFreeTransformMode()) {
        return;
    }

    if (!hasSelectionRegion()) {
        clearSelectionRegion();
        return;
    }
    pushUndoHistoryState();
    clearSelectionRegion();
}

void DrawingCanvas::setMaskPaintingEnabled(bool enabled)
{
    if (m_maskPaintingEnabled == enabled) return;
    if (m_isDrawing) endStroke();
    m_maskPaintingEnabled = enabled;
    update();
}

void DrawingCanvas::fillRasterLayerMask(int index, int grayscaleValue, bool selectionOnly)
{
    if (index < 0 || index >= m_layers.size()) return;
    RasterLayer &layer = m_layers[index];
    if (isRasterLayerEffectivelyLocked(index) || !isLayerEffectivelyVisible(index)
        || !layer.maskEnabled || layer.maskImage.isNull()) return;
    if (onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    pushUndoHistoryState();
    QPainter painter(&layer.maskImage);
    if (selectionOnly && m_hasSelectionRegion) painter.setClipRegion(m_selectionClipRegion);
    const int value = qBound(0, grayscaleValue, 255);
    painter.fillRect(layer.maskImage.rect(), QColor(value, value, value));
    painter.end();
    layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
}

void DrawingCanvas::selectAllWithHistory()
{
    if (m_documentSize.isEmpty()) {
        return;
    }
    const QRegion wholeDocument(QRect(QPoint(0, 0), m_documentSize));
    if (m_hasSelectionRegion && m_selectionClipRegion == wholeDocument) {
        return;
    }
    pushUndoHistoryState();
    setSelectionRegionInternal(wholeDocument, false);
    m_selectionPathCanvas = QPainterPath();
    m_selectionPathCanvas.addRect(QRectF(QPointF(0, 0), QSizeF(m_documentSize)));
    update();
}

void DrawingCanvas::invertSelectionWithHistory()
{
    if (m_documentSize.isEmpty()) return;
    const QRegion whole(QRect(QPoint(0, 0), m_documentSize));
    const QRegion current = hasSelectionRegion() ? m_selectionClipRegion : QRegion();
    const QRegion inverted = whole.subtracted(current);
    if (inverted == current) return;
    pushUndoHistoryState();
    setSelectionRegionInternal(inverted, false);
    m_selectionPathCanvas = QPainterPath();
    for (const QRect &rect : inverted) m_selectionPathCanvas.addRect(QRectF(rect));
    update();
}

bool DrawingCanvas::hasSelectionRegion() const
{
    return m_hasSelectionRegion && !m_selectionClipRegion.isEmpty();
}

bool DrawingCanvas::deleteSelectionPixelsWithHistory()
{
    if (!hasSelectionRegion() || m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) return false;
    RasterLayer &layer = m_layers[m_activeLayerIndex];
    if (layer.locked || !isLayerEffectivelyVisible(m_activeLayerIndex)
        || isGroupLayerType(layer.type) || isFillLayerType(layer.type)) return false;
    QImage *target = m_maskPaintingEnabled ? &layer.maskImage : &layer.image;
    if (target->isNull()) return false;
    pushUndoHistoryState();
    QPainter painter(target);
    painter.setRenderHint(QPainter::Antialiasing, false);
    painter.setClipRegion(m_selectionClipRegion);
    if (m_maskPaintingEnabled) painter.fillRect(target->rect(), Qt::black);
    else {
        painter.setCompositionMode(QPainter::CompositionMode_Clear);
        painter.fillRect(target->rect(), Qt::transparent);
    }
    painter.end();
    if (m_maskPaintingEnabled) layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
    return true;
}

bool DrawingCanvas::deletePixelsInUvFacesWithHistory(int index,
                                                     const QVector<QPointF> &uvPoints,
                                                     const QVector<quint32> &indices,
                                                     const QVector<int> &triangleIndices)
{
    if (index < 0 || index >= m_layers.size() || triangleIndices.isEmpty()) return false;
    RasterLayer &layer = m_layers[index];
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || isGroupLayerType(layer.type) || isFillLayerType(layer.type)) return false;
    QImage *target = m_maskPaintingEnabled ? &layer.maskImage : &layer.image;
    if (target->isNull()) return false;
    const int w = qMax(1, target->width() - 1), h = qMax(1, target->height() - 1);
    auto pixel = [w, h](const QPointF &uv) {
        return QPointF(qBound(0.0, uv.x(), 1.0) * w, (1.0 - qBound(0.0, uv.y(), 1.0)) * h);
    };
    QPainterPath path;
    for (int tri : triangleIndices) {
        const int base = tri * 3;
        if (tri < 0 || base + 2 >= indices.size()) continue;
        const quint32 a = indices[base], b = indices[base + 1], c = indices[base + 2];
        if (a >= quint32(uvPoints.size()) || b >= quint32(uvPoints.size()) || c >= quint32(uvPoints.size())) continue;
        QPainterPath triangle;
        triangle.moveTo(pixel(uvPoints[int(a)]));
        triangle.lineTo(pixel(uvPoints[int(b)]));
        triangle.lineTo(pixel(uvPoints[int(c)]));
        triangle.closeSubpath();
        path.addPath(triangle);
    }
    if (path.isEmpty()) return false;
    pushUndoHistoryState();
    QPainter painter(target);
    painter.setRenderHint(QPainter::Antialiasing, false);
    painter.setClipPath(path);
    if (m_maskPaintingEnabled) painter.fillRect(target->rect(), Qt::black);
    else {
        painter.setCompositionMode(QPainter::CompositionMode_Clear);
        painter.fillRect(target->rect(), Qt::transparent);
    }
    painter.end();
    if (m_maskPaintingEnabled) layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
    return true;
}

QImage DrawingCanvas::selectionMaskImage() const
{
    if (!hasSelectionRegion() || m_documentSize.isEmpty()) {
        return QImage();
    }

    QImage mask(m_documentSize, QImage::Format_Grayscale8);
    mask.fill(0);

    const QRect bounds(QPoint(0, 0), m_documentSize);
    for (const QRect &rect : m_selectionClipRegion) {
        const QRect clipped = rect.intersected(bounds);
        if (clipped.isEmpty()) {
            continue;
        }
        for (int y = clipped.top(); y <= clipped.bottom(); ++y) {
            uchar *line = mask.scanLine(y);
            std::memset(line + clipped.left(), 255, static_cast<size_t>(clipped.width()));
        }
    }

    return mask;
}

void DrawingCanvas::clearSelectionStateHard(bool triggerUpdate)
{
    endFreeTransformInteraction(false);
    resetFreeTransformSession();
    endSelectionTranslation(false);

    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    m_selectionPathCanvas = QPainterPath();
    m_selectionClipRegion = QRegion();
    m_hasSelectionRegion = false;
    updateSelectionAntsAnimationState();
    if (onSelectionRegionChanged) {
        onSelectionRegionChanged(false);
    }

    if (triggerUpdate) {
        update();
    }
}

DrawingCanvas::SelectionCombineMode DrawingCanvas::selectionCombineModeForModifiers(Qt::KeyboardModifiers modifiers) const
{
    if (modifiers.testFlag(Qt::AltModifier)) {
        return SelectionCombineMode::Subtract;
    }
    if (modifiers.testFlag(Qt::ShiftModifier)) {
        return SelectionCombineMode::Add;
    }
    return SelectionCombineMode::Replace;
}

QRegion DrawingCanvas::selectionRegionFromPath(const QPainterPath &path) const
{
    if (path.isEmpty()) {
        return QRegion();
    }

    QRegion region;
    const QList<QPolygonF> polys = path.toFillPolygons();
    for (const QPolygonF &polyf : polys) {
        if (polyf.size() < 3) {
            continue;
        }
        QPolygon poly;
        poly.reserve(polyf.size());
        for (const QPointF &p : polyf) {
            const int x = qBound(0, static_cast<int>(std::lround(p.x())), qMax(0, m_documentSize.width() - 1));
            const int y = qBound(0, static_cast<int>(std::lround(p.y())), qMax(0, m_documentSize.height() - 1));
            poly << QPoint(x, y);
        }
        if (poly.size() >= 3) {
            region = region.united(QRegion(poly, Qt::WindingFill));
        }
    }

    return region.intersected(QRegion(QRect(QPoint(0, 0), m_documentSize)));
}

void DrawingCanvas::setSelectionRegionInternal(const QRegion &region, bool triggerUpdate)
{
    const bool prev = m_hasSelectionRegion && !m_selectionClipRegion.isEmpty();
    m_selectionClipRegion = region.intersected(QRegion(QRect(QPoint(0, 0), m_documentSize)));
    m_hasSelectionRegion = !m_selectionClipRegion.isEmpty();

    if (!m_hasSelectionRegion) {
        m_selectionPathCanvas = QPainterPath();
    }

    updateSelectionAntsAnimationState();

    const bool next = m_hasSelectionRegion;
    if (prev != next && onSelectionRegionChanged) {
        onSelectionRegionChanged(next);
    }

    if (triggerUpdate) {
        update();
    }
}

void DrawingCanvas::applySelectionPolygon(const QVector<QPointF> &points, SelectionCombineMode combineMode)
{
    if (isFreeTransformMode()) {
        endFreeTransformInteraction(true);
    }

    if (points.size() < 3) {
        if (combineMode == SelectionCombineMode::Replace) {
            clearSelectionRegionWithHistory();
        }
        return;
    }

    QPolygon polygon;
    polygon.reserve(points.size());
    for (const QPointF &p : points) {
        const int x = qBound(0, static_cast<int>(std::lround(p.x())), qMax(0, m_documentSize.width() - 1));
        const int y = qBound(0, static_cast<int>(std::lround(p.y())), qMax(0, m_documentSize.height() - 1));
        polygon << QPoint(x, y);
    }

    if (polygon.size() < 3) {
        if (combineMode == SelectionCombineMode::Replace) {
            clearSelectionRegionWithHistory();
        }
        return;
    }

    QPainterPath polygonPath;
    polygonPath.moveTo(QPointF(polygon[0]));
    for (int i = 1; i < polygon.size(); ++i) {
        polygonPath.lineTo(QPointF(polygon[i]));
    }
    polygonPath.closeSubpath();
    polygonPath.setFillRule(Qt::WindingFill);

    const QPainterPath currentPath = m_selectionPathCanvas;
    QPainterPath nextPath;
    switch (combineMode) {
    case SelectionCombineMode::Replace:
        nextPath = polygonPath;
        break;
    case SelectionCombineMode::Add:
        nextPath = currentPath.united(polygonPath);
        break;
    case SelectionCombineMode::Subtract:
        nextPath = currentPath.subtracted(polygonPath);
        break;
    }
    nextPath.setFillRule(Qt::WindingFill);

    const QRegion nextRegion = selectionRegionFromPath(nextPath);
    const bool changed = (nextRegion != m_selectionClipRegion);
    if (!changed) {
        return;
    }

    pushUndoHistoryState();
    setSelectionRegionInternal(nextRegion, false);
    m_selectionPathCanvas = m_hasSelectionRegion ? nextPath : QPainterPath();
    if (isFreeTransformMode()) {
        refreshFreeTransformSession();
    }
    update();
}

bool DrawingCanvas::isNearSelectionBoundary(const QPointF &canvasPoint) const
{
    if (!hasSelectionRegion()) {
        return false;
    }

    if (m_selectionPathCanvas.isEmpty()) {
        return false;
    }

    QPainterPathStroker stroker;
    stroker.setWidth(6.0);
    const QPainterPath boundary = stroker.createStroke(m_selectionPathCanvas);
    return boundary.contains(canvasPoint);
}

bool DrawingCanvas::canMoveSelectionPixels() const
{
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return false;
    }
    const RasterLayer &layer = m_layers.at(m_activeLayerIndex);
    return !layer.locked && isLayerEffectivelyVisible(m_activeLayerIndex)
           && !isGroupLayerType(layer.type) && !isFillLayerType(layer.type);
}

bool DrawingCanvas::canMoveActiveLayerPixels() const
{
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return false;
    }
    const RasterLayer &layer = m_layers.at(m_activeLayerIndex);
    return !layer.locked && isLayerEffectivelyVisible(m_activeLayerIndex)
           && !isGroupLayerType(layer.type) && !isFillLayerType(layer.type);
}

void DrawingCanvas::beginSelectionTranslation(const QPointF &startCanvasPoint, bool movePixels)
{
    if (!hasSelectionRegion()) {
        return;
    }

    pushUndoHistoryState();
    m_selectionTranslationUndoPrimed = true;

    m_selectionTranslationActive = true;
    m_selectionTranslationMovePixels = movePixels;
    m_selectionTranslationAnchorCanvasPoint = startCanvasPoint;
    m_selectionTranslationOffset = QPoint(0, 0);
    m_selectionTranslationBaseRegion = m_selectionClipRegion;
    m_selectionTranslationBasePath = m_selectionPathCanvas;

    if (!movePixels) {
        return;
    }

    if (!canMoveSelectionPixels()) {
        m_selectionTranslationMovePixels = false;
        return;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        m_selectionTranslationMovePixels = false;
        return;
    }

    m_selectionTranslationLayerIndex = m_activeLayerIndex;
    m_selectionTranslationBaseLayerImage = *layerImage;
    m_selectionTranslationBackgroundImage = *layerImage;
    m_selectionTranslationCutoutImage = QImage(layerImage->size(), QImage::Format_ARGB32_Premultiplied);
    m_selectionTranslationCutoutImage.fill(Qt::transparent);

    QPainter extractPainter(&m_selectionTranslationCutoutImage);
    extractPainter.setClipRegion(m_selectionTranslationBaseRegion, Qt::IntersectClip);
    extractPainter.drawImage(QPoint(0, 0), *layerImage);
    extractPainter.end();

    QPainter clearPainter(&m_selectionTranslationBackgroundImage);
    clearPainter.setCompositionMode(QPainter::CompositionMode_Source);
    clearPainter.setClipRegion(m_selectionTranslationBaseRegion, Qt::IntersectClip);
    clearPainter.fillRect(layerImage->rect(), Qt::transparent);
    clearPainter.end();

    *layerImage = m_selectionTranslationBackgroundImage;
}

void DrawingCanvas::updateSelectionTranslation(const QPointF &canvasPoint)
{
    if (!m_selectionTranslationActive) {
        return;
    }

    const QPointF delta = canvasPoint - m_selectionTranslationAnchorCanvasPoint;
    const int dx = static_cast<int>(std::lround(delta.x()));
    const int dy = static_cast<int>(std::lround(delta.y()));
    const QPoint offset(dx, dy);
    if (offset == m_selectionTranslationOffset) {
        return;
    }
    m_selectionTranslationOffset = offset;

    QTransform translate;
    translate.translate(dx, dy);
    const QPainterPath movedPath = translate.map(m_selectionTranslationBasePath);
    const QRegion moved = selectionRegionFromPath(movedPath);
    setSelectionRegionInternal(moved, false);
    m_selectionPathCanvas = m_hasSelectionRegion ? movedPath : QPainterPath();

    if (m_selectionTranslationMovePixels && m_selectionTranslationLayerIndex == m_activeLayerIndex) {
        QImage *layerImage = activeLayerImage();
        if (layerImage && !layerImage->isNull()) {
            *layerImage = m_selectionTranslationBackgroundImage;
            QPainter p(layerImage);
            p.setCompositionMode(QPainter::CompositionMode_SourceOver);
            p.drawImage(offset, m_selectionTranslationCutoutImage);
            p.end();
            bumpContentRevision();
        }
    }

    update();
}

void DrawingCanvas::endSelectionTranslation(bool commit)
{
    if (!m_selectionTranslationActive) {
        return;
    }

    if (!commit) {
        const QRegion baseRegion = selectionRegionFromPath(m_selectionTranslationBasePath);
        setSelectionRegionInternal(baseRegion, false);
        m_selectionPathCanvas = m_hasSelectionRegion ? m_selectionTranslationBasePath : QPainterPath();
        if (m_selectionTranslationMovePixels && m_selectionTranslationLayerIndex == m_activeLayerIndex) {
            QImage *layerImage = activeLayerImage();
            if (layerImage && !m_selectionTranslationBaseLayerImage.isNull()) {
                *layerImage = m_selectionTranslationBaseLayerImage;
                bumpContentRevision();
            }
        }
        if (m_selectionTranslationUndoPrimed && !m_undoHistory.isEmpty()) {
            m_undoHistory.removeLast();
        }
    } else if (m_selectionTranslationUndoPrimed && m_selectionTranslationOffset == QPoint(0, 0)) {
        if (!m_undoHistory.isEmpty()) {
            m_undoHistory.removeLast();
        }
    }

    m_selectionTranslationActive = false;
    m_selectionTranslationMovePixels = false;
    m_selectionTranslationAnchorCanvasPoint = QPointF();
    m_selectionTranslationOffset = QPoint(0, 0);
    m_selectionTranslationBaseRegion = QRegion();
    m_selectionTranslationBasePath = QPainterPath();
    m_selectionTranslationBaseLayerImage = QImage();
    m_selectionTranslationBackgroundImage = QImage();
    m_selectionTranslationCutoutImage = QImage();
    m_selectionTranslationLayerIndex = -1;
    m_selectionTranslationUndoPrimed = false;

    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::beginLayerTranslation(const QPointF &startCanvasPoint)
{
    if (!canMoveActiveLayerPixels()) {
        return;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        return;
    }

    pushUndoHistoryState();
    m_layerTranslationUndoPrimed = true;

    m_layerTranslationActive = true;
    m_layerTranslationAnchorCanvasPoint = startCanvasPoint;
    m_layerTranslationOffset = QPoint(0, 0);
    m_layerTranslationLayerIndex = m_activeLayerIndex;
    m_layerTranslationBaseLayerImage = *layerImage;
}

void DrawingCanvas::updateLayerTranslation(const QPointF &canvasPoint)
{
    if (!m_layerTranslationActive) {
        return;
    }

    const QPointF delta = canvasPoint - m_layerTranslationAnchorCanvasPoint;
    const QPoint offset(static_cast<int>(std::lround(delta.x())),
                        static_cast<int>(std::lround(delta.y())));
    if (offset == m_layerTranslationOffset) {
        return;
    }
    m_layerTranslationOffset = offset;

    if (m_layerTranslationLayerIndex != m_activeLayerIndex) {
        return;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull() || m_layerTranslationBaseLayerImage.isNull()) {
        return;
    }

    QImage moved(layerImage->size(), QImage::Format_ARGB32_Premultiplied);
    moved.fill(Qt::transparent);
    QPainter p(&moved);
    p.setCompositionMode(QPainter::CompositionMode_SourceOver);
    p.drawImage(offset, m_layerTranslationBaseLayerImage);
    p.end();
    *layerImage = moved;
    bumpContentRevision();
    update();
}

void DrawingCanvas::endLayerTranslation(bool commit)
{
    if (!m_layerTranslationActive) {
        return;
    }

    if (!commit) {
        if (m_layerTranslationLayerIndex == m_activeLayerIndex) {
            QImage *layerImage = activeLayerImage();
            if (layerImage && !m_layerTranslationBaseLayerImage.isNull()) {
                *layerImage = m_layerTranslationBaseLayerImage;
                bumpContentRevision();
            }
        }
        if (m_layerTranslationUndoPrimed && !m_undoHistory.isEmpty()) {
            m_undoHistory.removeLast();
        }
    } else if (m_layerTranslationUndoPrimed && m_layerTranslationOffset == QPoint(0, 0)) {
        if (!m_undoHistory.isEmpty()) {
            m_undoHistory.removeLast();
        }
    }

    m_layerTranslationActive = false;
    m_layerTranslationAnchorCanvasPoint = QPointF();
    m_layerTranslationOffset = QPoint(0, 0);
    m_layerTranslationLayerIndex = -1;
    m_layerTranslationBaseLayerImage = QImage();
    m_layerTranslationUndoPrimed = false;
    resetFreeTransformSession();

    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

bool DrawingCanvas::isFreeTransformMode() const
{
    return m_selectionToolMode == QStringLiteral("free_transform");
}

void DrawingCanvas::resetFreeTransformSession()
{
    m_freeTransformSessionActive = false;
    m_freeTransformLayerIndex = -1;
    m_freeTransformBasePath = QPainterPath();
    m_freeTransformBaseRegion = QRegion();
    m_freeTransformBaseBounds = QRectF();
    m_freeTransformBaseLayerImage = QImage();
    m_freeTransformBackgroundImage = QImage();
    m_freeTransformCutoutImage = QImage();
    m_freeTransformPivotCanvasPoint = QPointF();
    m_freeTransformTranslationCanvas = QPointF();
    m_freeTransformRotationDegrees = 0.0;
    m_freeTransformScaleX = 1.0;
    m_freeTransformScaleY = 1.0;
    m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
    m_freeTransformActiveHandle = -1;
    m_freeTransformDragStartCanvasPoint = QPointF();
    m_freeTransformDragStartTranslationCanvas = QPointF();
    m_freeTransformDragStartPivotCanvasPoint = QPointF();
    m_freeTransformDragStartRotationDegrees = 0.0;
    m_freeTransformDragStartScaleX = 1.0;
    m_freeTransformDragStartScaleY = 1.0;
    m_freeTransformDragAnchorCanvasPoint = QPointF();
    m_freeTransformDragAlt = false;
    m_freeTransformUndoPrimed = false;
    m_freeTransformSessionUndoPrimed = false;
    m_freeTransformSessionOriginPivotCanvasPoint = QPointF();
    m_freeTransformSessionOriginPath = QPainterPath();
    m_freeTransformSessionOriginRegion = QRegion();
    m_freeTransformSessionOriginLayerImage = QImage();
}

void DrawingCanvas::refreshFreeTransformSession()
{
    if (!isFreeTransformMode() || !hasSelectionRegion() || !canMoveSelectionPixels()) {
        resetFreeTransformSession();
        return;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        resetFreeTransformSession();
        return;
    }

    m_freeTransformSessionActive = true;
    m_freeTransformLayerIndex = m_activeLayerIndex;
    m_freeTransformBasePath = canvasToViewAlignedPath(m_selectionPathCanvas);
    m_freeTransformBaseRegion = m_selectionClipRegion;
    m_freeTransformBaseBounds = m_freeTransformBasePath.boundingRect();
    if (m_freeTransformBaseBounds.isEmpty()) {
        const QRect bounds = m_freeTransformBaseRegion.boundingRect();
        m_freeTransformBaseBounds = QRectF(bounds.left(), bounds.top(), bounds.width(), bounds.height());
    }

    m_freeTransformBaseLayerImage = *layerImage;
    m_freeTransformBackgroundImage = *layerImage;
    m_freeTransformCutoutImage = QImage(layerImage->size(), QImage::Format_ARGB32_Premultiplied);
    m_freeTransformCutoutImage.fill(Qt::transparent);

    QPainter extractPainter(&m_freeTransformCutoutImage);
    extractPainter.setClipRegion(m_freeTransformBaseRegion, Qt::IntersectClip);
    extractPainter.drawImage(QPoint(0, 0), *layerImage);
    extractPainter.end();

    QPainter clearPainter(&m_freeTransformBackgroundImage);
    clearPainter.setCompositionMode(QPainter::CompositionMode_Source);
    clearPainter.setClipRegion(m_freeTransformBaseRegion, Qt::IntersectClip);
    clearPainter.fillRect(layerImage->rect(), Qt::transparent);
    clearPainter.end();

    m_freeTransformPivotCanvasPoint = m_freeTransformBaseBounds.center();
    m_freeTransformTranslationCanvas = QPointF();
    m_freeTransformRotationDegrees = 0.0;
    m_freeTransformScaleX = 1.0;
    m_freeTransformScaleY = 1.0;
    m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
    m_freeTransformActiveHandle = -1;
    m_freeTransformUndoPrimed = false;
    m_freeTransformSessionUndoPrimed = false;
    m_freeTransformSessionOriginPivotCanvasPoint = m_freeTransformPivotCanvasPoint;
    m_freeTransformSessionOriginPath = m_selectionPathCanvas;
    m_freeTransformSessionOriginRegion = m_freeTransformBaseRegion;
    m_freeTransformSessionOriginLayerImage = m_freeTransformBaseLayerImage;

    *layerImage = m_freeTransformBackgroundImage;
    QPainter restorePainter(layerImage);
    restorePainter.drawImage(QPoint(0, 0), m_freeTransformCutoutImage);
    restorePainter.end();
}

void DrawingCanvas::ensureFreeTransformUndoState()
{
    if (m_freeTransformSessionUndoPrimed) {
        return;
    }
    pushUndoHistoryState();
    m_freeTransformSessionUndoPrimed = true;
}

bool DrawingCanvas::hasEffectiveFreeTransformChange() const
{
    return (QLineF(m_freeTransformTranslationCanvas, QPointF()).length() > 0.01)
           || (std::abs(m_freeTransformRotationDegrees) > 0.01)
           || (std::abs(m_freeTransformScaleX - 1.0) > 0.0001)
           || (std::abs(m_freeTransformScaleY - 1.0) > 0.0001);
}

void DrawingCanvas::rebuildFreeTransformBaseFromCurrent(bool keepPivotWorldPoint)
{
    if (!m_freeTransformSessionActive || !hasSelectionRegion()) {
        return;
    }
    if (m_freeTransformLayerIndex != m_activeLayerIndex) {
        return;
    }

    QImage *layerImage = activeLayerImage();
    if (!layerImage || layerImage->isNull()) {
        return;
    }

    const QPointF pivotWorldBefore = freeTransformPivotWorldPoint(m_freeTransformTranslationCanvas);

    m_freeTransformBasePath = canvasToViewAlignedPath(m_selectionPathCanvas);
    m_freeTransformBaseRegion = m_selectionClipRegion;
    m_freeTransformBaseBounds = m_freeTransformBasePath.boundingRect();
    if (m_freeTransformBaseBounds.isEmpty()) {
        const QRect bounds = m_freeTransformBaseRegion.boundingRect();
        m_freeTransformBaseBounds = QRectF(bounds.left(), bounds.top(), bounds.width(), bounds.height());
    }

    m_freeTransformBaseLayerImage = *layerImage;
    m_freeTransformBackgroundImage = *layerImage;
    m_freeTransformCutoutImage = QImage(layerImage->size(), QImage::Format_ARGB32_Premultiplied);
    m_freeTransformCutoutImage.fill(Qt::transparent);

    QPainter extractPainter(&m_freeTransformCutoutImage);
    extractPainter.setClipRegion(m_freeTransformBaseRegion, Qt::IntersectClip);
    extractPainter.drawImage(QPoint(0, 0), *layerImage);
    extractPainter.end();

    QPainter clearPainter(&m_freeTransformBackgroundImage);
    clearPainter.setCompositionMode(QPainter::CompositionMode_Source);
    clearPainter.setClipRegion(m_freeTransformBaseRegion, Qt::IntersectClip);
    clearPainter.fillRect(layerImage->rect(), Qt::transparent);
    clearPainter.end();

    m_freeTransformTranslationCanvas = QPointF();
    m_freeTransformRotationDegrees = 0.0;
    m_freeTransformScaleX = 1.0;
    m_freeTransformScaleY = 1.0;
    if (keepPivotWorldPoint) {
        m_freeTransformPivotCanvasPoint = pivotWorldBefore;
    } else {
        m_freeTransformPivotCanvasPoint = m_freeTransformBaseBounds.center();
    }

    *layerImage = m_freeTransformBackgroundImage;
    QPainter restorePainter(layerImage);
    restorePainter.drawImage(QPoint(0, 0), m_freeTransformCutoutImage);
    restorePainter.end();
}

void DrawingCanvas::cancelFreeTransformSession()
{
    if (!m_freeTransformSessionActive) {
        return;
    }

    if (m_freeTransformLayerIndex == m_activeLayerIndex) {
        QImage *layerImage = activeLayerImage();
        if (layerImage && !m_freeTransformSessionOriginLayerImage.isNull()) {
            *layerImage = m_freeTransformSessionOriginLayerImage;
            bumpContentRevision();
        }
    }

    setSelectionRegionInternal(m_freeTransformSessionOriginRegion, false);
    m_selectionPathCanvas = m_hasSelectionRegion ? m_freeTransformSessionOriginPath : QPainterPath();

    if (m_freeTransformSessionUndoPrimed && !m_undoHistory.isEmpty()) {
        m_undoHistory.removeLast();
    }

    m_freeTransformPivotCanvasPoint = m_freeTransformSessionOriginPivotCanvasPoint;
    m_freeTransformTranslationCanvas = QPointF();
    m_freeTransformRotationDegrees = 0.0;
    m_freeTransformScaleX = 1.0;
    m_freeTransformScaleY = 1.0;
    m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
    m_freeTransformActiveHandle = -1;
    m_freeTransformUndoPrimed = false;
    m_freeTransformSessionUndoPrimed = false;

    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

QTransform DrawingCanvas::freeTransformMatrix() const
{
    QTransform t;
    t.translate(m_freeTransformTranslationCanvas.x(), m_freeTransformTranslationCanvas.y());
    t.translate(m_freeTransformPivotCanvasPoint.x(), m_freeTransformPivotCanvasPoint.y());
    t.rotate(m_freeTransformRotationDegrees);
    t.scale(m_freeTransformScaleX, m_freeTransformScaleY);
    t.translate(-m_freeTransformPivotCanvasPoint.x(), -m_freeTransformPivotCanvasPoint.y());
    return t;
}

void DrawingCanvas::applyFreeTransformPreview()
{
    if (!m_freeTransformSessionActive) {
        return;
    }

    const QTransform viewTransform = freeTransformMatrix();
    const QPainterPath movedPathView = viewTransform.map(m_freeTransformBasePath);
    const QPainterPath movedPath = viewAlignedToCanvasPath(movedPathView);
    const QRegion movedRegion = selectionRegionFromPath(movedPath);
    setSelectionRegionInternal(movedRegion, false);
    m_selectionPathCanvas = m_hasSelectionRegion ? movedPath : QPainterPath();

    if (m_freeTransformLayerIndex == m_activeLayerIndex) {
        QImage *layerImage = activeLayerImage();
        if (layerImage && !layerImage->isNull()) {
            *layerImage = m_freeTransformBackgroundImage;
            QPainter p(layerImage);
            p.setRenderHint(QPainter::SmoothPixmapTransform, true);
            const QTransform transform = viewAlignedToCanvasTransform()
                                         * viewTransform
                                         * canvasToViewAlignedTransform();
            p.setWorldTransform(transform, true);
            p.drawImage(QPoint(0, 0), m_freeTransformCutoutImage);
            p.end();
            bumpContentRevision();
        }
    }

    update();
}

QPointF DrawingCanvas::freeTransformHandleBasePoint(int handleIndex) const
{
    const qreal l = m_freeTransformBaseBounds.left();
    const qreal t = m_freeTransformBaseBounds.top();
    const qreal r = m_freeTransformBaseBounds.right();
    const qreal b = m_freeTransformBaseBounds.bottom();
    const qreal cx = (l + r) * 0.5;
    const qreal cy = (t + b) * 0.5;

    switch (handleIndex) {
    case 0: return QPointF(l, t);
    case 1: return QPointF(cx, t);
    case 2: return QPointF(r, t);
    case 3: return QPointF(r, cy);
    case 4: return QPointF(r, b);
    case 5: return QPointF(cx, b);
    case 6: return QPointF(l, b);
    case 7: return QPointF(l, cy);
    default: return QPointF();
    }
}

QPointF DrawingCanvas::freeTransformHandleWorldPoint(int handleIndex,
                                                     qreal scaleX,
                                                     qreal scaleY,
                                                     qreal rotationDegrees,
                                                     const QPointF &translation) const
{
    QTransform t;
    t.translate(translation.x(), translation.y());
    t.translate(m_freeTransformPivotCanvasPoint.x(), m_freeTransformPivotCanvasPoint.y());
    t.rotate(rotationDegrees);
    t.scale(scaleX, scaleY);
    t.translate(-m_freeTransformPivotCanvasPoint.x(), -m_freeTransformPivotCanvasPoint.y());
    return t.map(freeTransformHandleBasePoint(handleIndex));
}

QPointF DrawingCanvas::freeTransformPivotWorldPoint(const QPointF &translation) const
{
    return m_freeTransformPivotCanvasPoint + translation;
}

QVector<QPointF> DrawingCanvas::freeTransformHandlePoints() const
{
    QVector<QPointF> points;
    points.reserve(8);
    for (int i = 0; i < 8; ++i) {
        points.push_back(freeTransformHandleWorldPoint(i,
                                                       m_freeTransformScaleX,
                                                       m_freeTransformScaleY,
                                                       m_freeTransformRotationDegrees,
                                                       m_freeTransformTranslationCanvas));
    }
    return points;
}

int DrawingCanvas::freeTransformHandleAt(const QPointF &canvasPoint) const
{
    const QRect art = documentDisplayRect();
    const qreal canvasUnitsPerWidgetPixel = qMax(
        static_cast<qreal>(qMax(1, m_documentSize.width() - 1)) / qMax(1, art.width() - 1),
        static_cast<qreal>(qMax(1, m_documentSize.height() - 1)) / qMax(1, art.height() - 1));
    const qreal hitRadius = qMax(1.0, 11.0 * canvasUnitsPerWidgetPixel);
    const QVector<QPointF> handles = freeTransformHandlePoints();
    for (int i = 0; i < handles.size(); ++i) {
        if (QLineF(handles[i], canvasPoint).length() <= hitRadius) {
            return i;
        }
    }
    return -1;
}

int DrawingCanvas::freeTransformOppositeHandleIndex(int handleIndex) const
{
    switch (handleIndex) {
    case 0: return 4;
    case 1: return 5;
    case 2: return 6;
    case 3: return 7;
    case 4: return 0;
    case 5: return 1;
    case 6: return 2;
    case 7: return 3;
    default: return -1;
    }
}

bool DrawingCanvas::freeTransformPointNearPivot(const QPointF &canvasPoint) const
{
    const QRect art = documentDisplayRect();
    const qreal canvasUnitsPerWidgetPixel = qMax(
        static_cast<qreal>(qMax(1, m_documentSize.width() - 1)) / qMax(1, art.width() - 1),
        static_cast<qreal>(qMax(1, m_documentSize.height() - 1)) / qMax(1, art.height() - 1));
    const QPointF pivot = freeTransformPivotWorldPoint(m_freeTransformTranslationCanvas);
    return QLineF(pivot, canvasPoint).length() <= qMax(1.0, 10.0 * canvasUnitsPerWidgetPixel);
}

bool DrawingCanvas::freeTransformPointNearRotationRing(const QPointF &canvasPoint) const
{
    if (!m_freeTransformSessionActive) {
        return false;
    }

    const QRect art = documentDisplayRect();
    const qreal canvasUnitsPerWidgetPixel = qMax(
        static_cast<qreal>(qMax(1, m_documentSize.width() - 1)) / qMax(1, art.width() - 1),
        static_cast<qreal>(qMax(1, m_documentSize.height() - 1)) / qMax(1, art.height() - 1));
    const QPointF topCenter = freeTransformHandleWorldPoint(1,
                                                             m_freeTransformScaleX,
                                                             m_freeTransformScaleY,
                                                             m_freeTransformRotationDegrees,
                                                             m_freeTransformTranslationCanvas);
    const QPointF transformedCenter = freeTransformMatrix().map(m_freeTransformBaseBounds.center());
    QLineF outward(transformedCenter, topCenter);
    if (outward.length() < 0.001) return false;
    outward.setLength(outward.length() + 34.0 * canvasUnitsPerWidgetPixel);
    const QPointF rotationHandle = outward.p2();
    return QLineF(rotationHandle, canvasPoint).length() <= 11.0 * canvasUnitsPerWidgetPixel;
}

bool DrawingCanvas::freeTransformPointInside(const QPointF &canvasPoint) const
{
    if (!m_freeTransformSessionActive) {
        return false;
    }
    QPainterPath box;
    box.addRect(m_freeTransformBaseBounds);
    return freeTransformMatrix().map(box).contains(canvasPoint);
}

void DrawingCanvas::beginFreeTransformInteraction(const QPointF &canvasPoint, Qt::KeyboardModifiers modifiers)
{
    if (!m_freeTransformSessionActive) {
        refreshFreeTransformSession();
    }
    if (!m_freeTransformSessionActive) {
        return;
    }

    const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);

    m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
    m_freeTransformActiveHandle = -1;
    m_freeTransformDragStartCanvasPoint = viewPoint;
    m_freeTransformDragStartTranslationCanvas = m_freeTransformTranslationCanvas;
    m_freeTransformDragStartPivotCanvasPoint = m_freeTransformPivotCanvasPoint;
    m_freeTransformDragStartRotationDegrees = m_freeTransformRotationDegrees;
    m_freeTransformDragStartScaleX = m_freeTransformScaleX;
    m_freeTransformDragStartScaleY = m_freeTransformScaleY;
    m_freeTransformDragAlt = modifiers.testFlag(Qt::AltModifier);

    if (freeTransformPointNearPivot(viewPoint)) {
        m_freeTransformInteractionMode = FreeTransformInteractionMode::Pivot;
        return;
    }

    const int handleIndex = freeTransformHandleAt(viewPoint);
    if (handleIndex >= 0) {
        m_freeTransformInteractionMode = FreeTransformInteractionMode::Scale;
        m_freeTransformActiveHandle = handleIndex;
        if (m_freeTransformDragAlt) {
            m_freeTransformDragAnchorCanvasPoint = freeTransformPivotWorldPoint(m_freeTransformDragStartTranslationCanvas);
        } else {
            const int opposite = freeTransformOppositeHandleIndex(handleIndex);
            m_freeTransformDragAnchorCanvasPoint = freeTransformHandleWorldPoint(opposite,
                                                                                 m_freeTransformDragStartScaleX,
                                                                                 m_freeTransformDragStartScaleY,
                                                                                 m_freeTransformDragStartRotationDegrees,
                                                                                 m_freeTransformDragStartTranslationCanvas);
        }
        ensureFreeTransformUndoState();
        m_freeTransformUndoPrimed = true;
        return;
    }

    if (freeTransformPointInside(viewPoint)) {
        m_freeTransformInteractionMode = FreeTransformInteractionMode::Move;
        ensureFreeTransformUndoState();
        m_freeTransformUndoPrimed = true;
        return;
    }

    if (freeTransformPointNearRotationRing(viewPoint)) {
        m_freeTransformInteractionMode = FreeTransformInteractionMode::Rotate;
        ensureFreeTransformUndoState();
        m_freeTransformUndoPrimed = true;
    }
}

void DrawingCanvas::updateFreeTransformInteraction(const QPointF &canvasPoint, Qt::KeyboardModifiers modifiers)
{
    if (!m_freeTransformSessionActive || m_freeTransformInteractionMode == FreeTransformInteractionMode::None) {
        return;
    }

    const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);

    if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Pivot) {
        const QPointF delta = viewPoint - m_freeTransformDragStartCanvasPoint;
        const QPointF nextPivot = m_freeTransformDragStartPivotCanvasPoint + delta;

        const qreal rad = m_freeTransformRotationDegrees * 3.14159265358979323846 / 180.0;
        const QPointF axisX(std::cos(rad) * m_freeTransformScaleX, std::sin(rad) * m_freeTransformScaleX);
        const QPointF axisY(-std::sin(rad) * m_freeTransformScaleY, std::cos(rad) * m_freeTransformScaleY);
        auto linearMap = [&](const QPointF &p) {
            return QPointF(axisX.x() * p.x() + axisY.x() * p.y(),
                           axisX.y() * p.x() + axisY.y() * p.y());
        };

        const QPointF oldPivot = m_freeTransformPivotCanvasPoint;
        const QPointF oldConst = oldPivot - linearMap(oldPivot);
        const QPointF newConst = nextPivot - linearMap(nextPivot);
        const QPointF translationDelta = oldConst - newConst;

        m_freeTransformPivotCanvasPoint = nextPivot;
        m_freeTransformTranslationCanvas += translationDelta;
        applyFreeTransformPreview();
        return;
    }

    if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Move) {
        const QPointF delta = viewPoint - m_freeTransformDragStartCanvasPoint;
        m_freeTransformTranslationCanvas = m_freeTransformDragStartTranslationCanvas + delta;
        applyFreeTransformPreview();
        return;
    }

    if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Rotate) {
        const QPointF pivotWorld = freeTransformPivotWorldPoint(m_freeTransformDragStartTranslationCanvas);
        const qreal startAngle = std::atan2(m_freeTransformDragStartCanvasPoint.y() - pivotWorld.y(),
                                            m_freeTransformDragStartCanvasPoint.x() - pivotWorld.x());
        const qreal currentAngle = std::atan2(viewPoint.y() - pivotWorld.y(),
                              viewPoint.x() - pivotWorld.x());
        const qreal deltaDeg = normalizeDegrees((currentAngle - startAngle) * 180.0 / 3.14159265358979323846);
        m_freeTransformRotationDegrees = snappedRotationDegrees(m_freeTransformDragStartRotationDegrees + deltaDeg);
        applyFreeTransformPreview();
        return;
    }

    if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Scale && m_freeTransformActiveHandle >= 0) {
        const bool keepAspect = modifiers.testFlag(Qt::ShiftModifier);
        const bool scaleFromPivot = modifiers.testFlag(Qt::AltModifier);

        const qreal rad = m_freeTransformDragStartRotationDegrees * 3.14159265358979323846 / 180.0;
        const QPointF axisX(std::cos(rad), std::sin(rad));
        const QPointF axisY(-std::sin(rad), std::cos(rad));

        QPointF anchor = m_freeTransformDragAnchorCanvasPoint;
        QPointF anchorBase = m_freeTransformDragStartPivotCanvasPoint;
        if (!scaleFromPivot) {
            const int opposite = freeTransformOppositeHandleIndex(m_freeTransformActiveHandle);
            anchorBase = freeTransformHandleBasePoint(opposite);
            anchor = freeTransformHandleWorldPoint(opposite,
                                                   m_freeTransformDragStartScaleX,
                                                   m_freeTransformDragStartScaleY,
                                                   m_freeTransformDragStartRotationDegrees,
                                                   m_freeTransformDragStartTranslationCanvas);
        } else {
            anchorBase = m_freeTransformDragStartPivotCanvasPoint;
            anchor = freeTransformPivotWorldPoint(m_freeTransformDragStartTranslationCanvas);
        }

        const QPointF handleStart = freeTransformHandleWorldPoint(m_freeTransformActiveHandle,
                                                                   m_freeTransformDragStartScaleX,
                                                                   m_freeTransformDragStartScaleY,
                                                                   m_freeTransformDragStartRotationDegrees,
                                                                   m_freeTransformDragStartTranslationCanvas);
        const QPointF baseVec = handleStart - anchor;
        const QPointF currVec = viewPoint - anchor;

        const qreal baseX = dot2(baseVec, axisX);
        const qreal baseY = dot2(baseVec, axisY);
        const qreal currX = dot2(currVec, axisX);
        const qreal currY = dot2(currVec, axisY);

        qreal ratioX = (std::abs(baseX) > 0.0001) ? (currX / baseX) : 1.0;
        qreal ratioY = (std::abs(baseY) > 0.0001) ? (currY / baseY) : 1.0;

        const bool affectsX = (m_freeTransformActiveHandle == 0
                               || m_freeTransformActiveHandle == 2
                               || m_freeTransformActiveHandle == 3
                               || m_freeTransformActiveHandle == 4
                               || m_freeTransformActiveHandle == 6
                               || m_freeTransformActiveHandle == 7);
        const bool affectsY = (m_freeTransformActiveHandle == 0
                               || m_freeTransformActiveHandle == 1
                               || m_freeTransformActiveHandle == 2
                               || m_freeTransformActiveHandle == 4
                               || m_freeTransformActiveHandle == 5
                               || m_freeTransformActiveHandle == 6);

        if (keepAspect) {
            qreal uniformRatio = 1.0;
            if (affectsX && affectsY) {
                uniformRatio = (std::abs(ratioX) >= std::abs(ratioY)) ? ratioX : ratioY;
            } else if (affectsX) {
                uniformRatio = ratioX;
            } else if (affectsY) {
                uniformRatio = ratioY;
            }
            ratioX = uniformRatio;
            ratioY = uniformRatio;
        }

        qreal nextScaleX = m_freeTransformDragStartScaleX;
        qreal nextScaleY = m_freeTransformDragStartScaleY;
        if (affectsX) {
            nextScaleX = clampScaleSigned(m_freeTransformDragStartScaleX * ratioX);
            if (keepAspect && !affectsY) {
                nextScaleY = clampScaleSigned(m_freeTransformDragStartScaleY * ratioX);
            }
        }
        if (affectsY) {
            nextScaleY = clampScaleSigned(m_freeTransformDragStartScaleY * ratioY);
            if (keepAspect && !affectsX) {
                nextScaleX = clampScaleSigned(m_freeTransformDragStartScaleX * ratioY);
            }
        }

        m_freeTransformScaleX = nextScaleX;
        m_freeTransformScaleY = nextScaleY;
        m_freeTransformRotationDegrees = m_freeTransformDragStartRotationDegrees;
        m_freeTransformPivotCanvasPoint = m_freeTransformDragStartPivotCanvasPoint;

        QTransform noTranslate;
        noTranslate.translate(m_freeTransformPivotCanvasPoint.x(), m_freeTransformPivotCanvasPoint.y());
        noTranslate.rotate(m_freeTransformRotationDegrees);
        noTranslate.scale(m_freeTransformScaleX, m_freeTransformScaleY);
        noTranslate.translate(-m_freeTransformPivotCanvasPoint.x(), -m_freeTransformPivotCanvasPoint.y());
        const QPointF mappedAnchor = noTranslate.map(anchorBase);
        m_freeTransformTranslationCanvas = anchor - mappedAnchor;

        applyFreeTransformPreview();
    }
}

void DrawingCanvas::endFreeTransformInteraction(bool commit)
{
    if (!m_freeTransformSessionActive) {
        m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
        m_freeTransformActiveHandle = -1;
        return;
    }

    const bool changed = hasEffectiveFreeTransformChange();

    if (!commit) {
        if (m_freeTransformLayerIndex == m_activeLayerIndex) {
            QImage *layerImage = activeLayerImage();
            if (layerImage && !m_freeTransformBaseLayerImage.isNull()) {
                *layerImage = m_freeTransformBaseLayerImage;
                bumpContentRevision();
            }
        }
        setSelectionRegionInternal(m_freeTransformBaseRegion, false);
        m_selectionPathCanvas = m_hasSelectionRegion ? viewAlignedToCanvasPath(m_freeTransformBasePath) : QPainterPath();
        if (m_freeTransformUndoPrimed && !m_undoHistory.isEmpty()) {
            m_undoHistory.removeLast();
        }
    } else if (m_freeTransformUndoPrimed && !changed) {
        m_freeTransformTranslationCanvas = QPointF();
        m_freeTransformRotationDegrees = 0.0;
        m_freeTransformScaleX = 1.0;
        m_freeTransformScaleY = 1.0;
    }

    m_freeTransformInteractionMode = FreeTransformInteractionMode::None;
    m_freeTransformActiveHandle = -1;
    m_freeTransformUndoPrimed = false;

    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::cancelSelectionConstruction()
{
    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    updateSelectionAntsAnimationState();
    update();
}

void DrawingCanvas::updateSelectionAntsAnimationState()
{
    const bool active = hasSelectionRegion() || !m_selectionWorkingPoints.isEmpty() || m_selectionTranslationActive;
    if (active) {
        if (!m_selectionAntsTimer.isActive()) {
            m_selectionAntsTimer.start();
        }
    } else if (m_selectionAntsTimer.isActive()) {
        m_selectionAntsTimer.stop();
    }
}

bool DrawingCanvas::triggerActiveLayerMaskBlink()
{
    ensureLayers();
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return false;
    }

    const RasterLayer &layer = m_layers.at(m_activeLayerIndex);
    if (!layer.maskEnabled || layer.maskImage.isNull()) {
        return false;
    }

    m_maskBlinkActive = true;
    m_maskBlinkFadeOut = false;
    m_maskBlinkElapsed.restart();
    if (!m_maskBlinkFrameTimer.isActive()) {
        m_maskBlinkFrameTimer.start();
    }
    update();
    return true;
}

bool DrawingCanvas::beginActiveLayerMaskPreviewHold()
{
    ensureLayers();
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) return false;
    const RasterLayer &layer = m_layers.at(m_activeLayerIndex);
    if (!layer.maskEnabled || layer.maskImage.isNull()) return false;
    m_maskPreviewHeld = true;
    m_maskBlinkActive = false;
    m_maskBlinkFrameTimer.stop();
    update();
    return true;
}

void DrawingCanvas::endActiveLayerMaskPreviewHold()
{
    if (!m_maskPreviewHeld) return;
    m_maskPreviewHeld = false;
    m_maskBlinkActive = false;
    m_maskBlinkFadeOut = false;
    m_maskBlinkFrameTimer.stop();
    update();
}

void DrawingCanvas::applySolidColorToSelection(int index, const QColor &color)
{
    if (index < 0 || index >= m_layers.size() || !color.isValid() || !hasSelectionRegion()) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || isGroupLayerType(layer.type) || isFillLayerType(layer.type)) {
        return;
    }

    pushUndoHistoryState();
    QPainter painter(&layer.image);
    painter.setRenderHint(QPainter::Antialiasing, true);
    if (layer.transparentPixelsLocked) {
        painter.setCompositionMode(QPainter::CompositionMode_SourceAtop);
    }
    painter.setClipRegion(m_selectionClipRegion, Qt::IntersectClip);
    painter.fillRect(layer.image.rect(), color);
    painter.end();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::applyGradientToSelection(int index,
                                             const QPointF &startCanvas,
                                             const QPointF &endCanvas,
                                             const QColor &startColor,
                                             const QColor &endColor)
{
    if (index < 0 || index >= m_layers.size() || !startColor.isValid() || !endColor.isValid() || !hasSelectionRegion()) {
        return;
    }

    RasterLayer &layer = m_layers[index];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) {
        return;
    }

    QPointF startPx = startCanvas;
    QPointF endPx = endCanvas;
    if (QLineF(startPx, endPx).length() < 0.001) {
        endPx += QPointF(targetImage->width(), 0.0);
    }
    QLinearGradient gradient(startPx, endPx);
    const QColor gradientStart = editingMask
                                     ? QColor(qGray(startColor.rgb()), qGray(startColor.rgb()), qGray(startColor.rgb()))
                                     : startColor;
    const QColor gradientEnd = editingMask
                                   ? QColor(qGray(endColor.rgb()), qGray(endColor.rgb()), qGray(endColor.rgb()))
                                   : endColor;
    gradient.setColorAt(0.0, gradientStart);
    gradient.setColorAt(1.0, gradientEnd);

    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (!editingMask) pushUndoHistoryState();
    QPainter painter(targetImage);
    painter.setRenderHint(QPainter::Antialiasing, true);
    painter.setClipRegion(m_selectionClipRegion, Qt::IntersectClip);
    painter.fillRect(targetImage->rect(), gradient);
    painter.end();
    if (editingMask) layer.meshMaskFaceIndices.clear();

    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::applyGradientToLayer(int index,
                                         const QPointF &startCanvas,
                                         const QPointF &endCanvas,
                                         const QColor &startColor,
                                         const QColor &endColor)
{
    if (index < 0 || index >= m_layers.size() || !startColor.isValid() || !endColor.isValid()) {
        return;
    }
    RasterLayer &layer = m_layers[index];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (layer.locked || !isLayerEffectivelyVisible(index)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) {
        return;
    }
    QPointF endPoint = endCanvas;
    if (QLineF(startCanvas, endPoint).length() < 0.001) {
        endPoint += QPointF(targetImage->width(), 0.0);
    }
    QLinearGradient gradient(startCanvas, endPoint);
    const QColor gradientStart = editingMask
                                     ? QColor(qGray(startColor.rgb()), qGray(startColor.rgb()), qGray(startColor.rgb()))
                                     : startColor;
    const QColor gradientEnd = editingMask
                                   ? QColor(qGray(endColor.rgb()), qGray(endColor.rgb()), qGray(endColor.rgb()))
                                   : endColor;
    gradient.setColorAt(0.0, gradientStart);
    gradient.setColorAt(1.0, gradientEnd);
    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    if (!editingMask) pushUndoHistoryState();
    QPainter painter(targetImage);
    painter.fillRect(targetImage->rect(), gradient);
    painter.end();
    if (editingMask) layer.meshMaskFaceIndices.clear();
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

void DrawingCanvas::paintEvent(QPaintEvent *event)
{
    Q_UNUSED(event);
    ensureLayers();

    QPainter painter(this);
    const QRect previewRect = canvasRect();
    const QRect artRect = documentDisplayRect();
    painter.setCompositionMode(QPainter::CompositionMode_Source);
    painter.fillRect(rect(), workspaceColor());
    painter.setCompositionMode(QPainter::CompositionMode_SourceOver);

    auto isEffectivelyVisible = [this](int layerIndex) {
        if (layerIndex < 0 || layerIndex >= m_layers.size()) {
            return false;
        }
        int guard = 0;
        int cursor = layerIndex;
        while (cursor >= 0 && cursor < m_layers.size() && guard < m_layers.size()) {
            const RasterLayer &probe = m_layers.at(cursor);
            if (!probe.visible) {
                return false;
            }
            cursor = probe.parentIndex;
            ++guard;
        }
        return true;
    };

    bool hasVisibleFillLayer = false;
    for (int i = 0; i < m_layers.size(); ++i) {
        if (isFillLayerType(m_layers.at(i).type) && isEffectivelyVisible(i)) {
            hasVisibleFillLayer = true;
            break;
        }
    }

    painter.save();
    painter.translate(artRect.center());
    painter.rotate(m_viewRotationDegrees);
    painter.translate(-artRect.center());

    const QRect shadowRect = previewRect.adjusted(5, 6, 5, 6);
    painter.fillRect(shadowRect, m_outlineShadowColor);

    if (hasVisibleFillLayer) {
        painter.fillRect(previewRect, Qt::white);
    } else {
        const int tile = 16;
        const QColor c0(224, 224, 224);
        const QColor c1(188, 188, 188);
        for (int y = previewRect.top(); y <= previewRect.bottom(); y += tile) {
            for (int x = previewRect.left(); x <= previewRect.right(); x += tile) {
                const bool even = (((x - previewRect.left()) / tile) + ((y - previewRect.top()) / tile)) % 2 == 0;
                painter.fillRect(QRect(x, y, tile, tile), even ? c0 : c1);
            }
        }
    }

    // Normal flat raster stacks can be drawn directly into the widget's dirty
    // region. This avoids the two full-document cache builds that previously
    // happened on pen-down, while retaining the actual layer order.
    const bool canDrawTransientLayerDirectly = !m_externalUvStrokeActive
                                               && !m_maskPaintingEnabled
                                               && canDrawFlatStrokeStackDirectly()
                                               && m_activeLayerIndex >= 0
                                               && m_activeLayerIndex < m_layers.size();
    // In mask edit mode the grayscale mask is drawn below. Building the full
    // layer composite first would be hidden by it, so skip that work entirely.
    if (m_maskEditPreviewEnabled) {
        // The checkerboard background prepared above remains visible.
    } else if (m_tilingPreviewEnabled) {
        const QImage composed = composeLayersForDisplay();
        for (int tileY = -1; tileY <= 1; ++tileY) {
            for (int tileX = -1; tileX <= 1; ++tileX) {
                painter.drawImage(artRect.translated(tileX * artRect.width(), tileY * artRect.height()), composed);
            }
        }
        painter.setPen(QPen(QColor(255, 196, 92, 220), 2.0));
        painter.setBrush(Qt::NoBrush);
        painter.drawRect(artRect.adjusted(1, 1, -1, -1));
    } else if (canDrawTransientLayerDirectly) {
        for (int i = 0; i < m_layers.size(); ++i) {
            const RasterLayer &layer = m_layers.at(i);
            if (!layer.visible) continue;
            painter.drawImage(artRect, m_nonAccumulatingStrokeActive && i == m_activeLayerIndex
                                         ? m_strokePreviewLayerImage
                                         : layer.image);
        }
    } else {
        const QImage composed = composeLayersForDisplay();
        painter.drawImage(artRect, composed);
    }

    auto drawActiveMaskOverlay = [&](int maxAlpha) {
        if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
            return;
        }
        const RasterLayer &layer = m_layers[m_activeLayerIndex];
        if (!layer.maskEnabled || layer.maskImage.isNull()) {
            return;
        }

        const QImage &maskSource = (m_maskPaintingEnabled && m_nonAccumulatingStrokeActive
                                    && !m_maskStrokePreviewImage.isNull())
                                       ? m_maskStrokePreviewImage
                                       : layer.maskImage;
        QImage mask = maskSource.convertToFormat(QImage::Format_Grayscale8);
        if (mask.size() != m_documentSize) {
            mask = mask.scaled(m_documentSize, Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
        }

        QImage overlay(mask.size(), QImage::Format_ARGB32_Premultiplied);
        overlay.fill(Qt::transparent);

        const int clampedMaxAlpha = qBound(0, maxAlpha, 255);
        for (int y = 0; y < overlay.height(); ++y) {
            QRgb *dst = reinterpret_cast<QRgb *>(overlay.scanLine(y));
            const uchar *maskLine = mask.constScanLine(y);
            for (int x = 0; x < overlay.width(); ++x) {
                const int hidden = 255 - static_cast<int>(maskLine[x]);
                if (hidden <= 0) {
                    dst[x] = qRgba(0, 0, 0, 0);
                    continue;
                }

                const int alpha = (clampedMaxAlpha * hidden + 127) / 255;
                dst[x] = qPremultiply(qRgba(220, 28, 28, alpha));
            }
        }

        painter.drawImage(artRect, overlay);
    };

    if (m_maskEditPreviewEnabled && m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        const RasterLayer &layer = m_layers.at(m_activeLayerIndex);
        const QImage &maskSource = (m_maskPaintingEnabled && m_nonAccumulatingStrokeActive
                                    && !m_maskStrokePreviewImage.isNull())
                                       ? m_maskStrokePreviewImage
                                       : layer.maskImage;
        if (layer.maskEnabled && !maskSource.isNull()) {
            // Mask editing is image editing: show the actual grayscale mask,
            // not the composited layer with a selection-style tint over it.
            painter.drawImage(artRect, maskSource);
        }
    }

    if (m_maskPreviewHeld) {
        drawActiveMaskOverlay(230);
    }

    if (m_maskBlinkActive && !m_maskPreviewHeld) {
        const qreal progress = qBound(0.0,
                                      static_cast<qreal>(m_maskBlinkElapsed.elapsed())
                                          / static_cast<qreal>(qMax(1, m_maskBlinkDurationMs)),
                                      1.0);
        const qreal envelope = m_maskBlinkFadeOut
                                   ? (1.0 - progress)
                                   : std::sin(progress * 3.14159265358979323846);
        const int blinkAlpha = static_cast<int>(std::round(230.0 * qBound(0.0, envelope, 1.0)));
        if (blinkAlpha > 0) {
            drawActiveMaskOverlay(blinkAlpha);
        }
        if (progress >= 1.0) {
            m_maskBlinkActive = false;
            m_maskBlinkFadeOut = false;
            m_maskBlinkFrameTimer.stop();
        }
    }

    if (m_uvOverlayVisible && !m_uvOverlayPoints.isEmpty() && m_uvOverlayIndices.size() >= 3) {
        const QImage &overlay = uvOverlaySnapshot(artRect.size());
        if (!overlay.isNull()) painter.drawImage(artRect.topLeft(), overlay);
    }

    auto canvasToArtPoint = [this, &artRect](const QPointF &canvasPoint) {
        const qreal nx = qBound(0.0, canvasPoint.x() / qMax(1, m_documentSize.width() - 1), 1.0);
        const qreal ny = qBound(0.0, canvasPoint.y() / qMax(1, m_documentSize.height() - 1), 1.0);
        return QPointF(artRect.left() + nx * qMax(1, artRect.width() - 1),
                       artRect.top() + ny * qMax(1, artRect.height() - 1));
    };

    auto canvasToArtPointUnclamped = [this, &artRect](const QPointF &canvasPoint) {
        const qreal nx = canvasPoint.x() / qMax(1, m_documentSize.width() - 1);
        const qreal ny = canvasPoint.y() / qMax(1, m_documentSize.height() - 1);
        return QPointF(artRect.left() + nx * qMax(1, artRect.width() - 1),
                        artRect.top() + ny * qMax(1, artRect.height() - 1));
    };

    if (m_bucketGradientPreviewVisible) {
        const QPointF start = canvasToArtPointUnclamped(m_bucketGradientPreviewStart);
        const QPointF end = canvasToArtPointUnclamped(m_bucketGradientPreviewEnd);
        painter.save();
        painter.setRenderHint(QPainter::Antialiasing, true);
        painter.setPen(QPen(QColor(14, 18, 24, 220), 4.0, Qt::SolidLine, Qt::RoundCap));
        painter.drawLine(start, end);
        painter.setPen(QPen(QColor(245, 250, 255, 245), 1.5, Qt::SolidLine, Qt::RoundCap));
        painter.drawLine(start, end);
        painter.setBrush(m_brushInkColor);
        painter.setPen(QPen(Qt::white, 1.5));
        painter.drawEllipse(start, 5.0, 5.0);
        painter.restore();
    }

    if (m_symmetryEnabled && !m_selectionToolEnabled && m_symmetrySegments > 1) {
        painter.setRenderHint(QPainter::Antialiasing, true);
        painter.save();
        painter.setClipRect(artRect, Qt::IntersectClip);

        const QPointF centerCanvas = symmetryCenterCanvasPoint();
        const QPointF centerArt = canvasToArtPoint(centerCanvas);
        const qreal farRadius = std::hypot(static_cast<qreal>(m_documentSize.width()),
                                           static_cast<qreal>(m_documentSize.height()))
                                * 1.35;
        int segments = qBound(2, m_symmetrySegments, 8);
        if ((segments % 2) != 0) {
            segments = qMin(8, segments + 1);
        }

        QColor baseGuide = m_symmetryGuideColor;
        if (!baseGuide.isValid()) {
            baseGuide = QColor(255, 59, 48, 190);
        }
        QColor primaryAxisColor = baseGuide;
        primaryAxisColor.setAlpha(qBound(24, baseGuide.alpha(), 255));
        QColor secondaryAxisColor = baseGuide;
        secondaryAxisColor.setAlpha(qBound(18, static_cast<int>(baseGuide.alpha() * 0.78), 230));
        QColor linkColor = baseGuide;
        linkColor.setAlpha(qBound(18, static_cast<int>(baseGuide.alpha() * 0.90), 245));
        QColor centerFillColor = baseGuide.lighter(132);
        centerFillColor.setAlpha(qBound(36, static_cast<int>(baseGuide.alpha() * 1.08), 255));
        QColor centerStrokeColor = baseGuide.darker(230);
        centerStrokeColor.setAlpha(qBound(48, static_cast<int>(baseGuide.alpha() * 1.10), 255));
        QColor handleFillColor = baseGuide;
        handleFillColor.setAlpha(qBound(48, static_cast<int>(baseGuide.alpha() * 1.15), 255));
        QColor handleStrokeColor = baseGuide.darker(180);
        handleStrokeColor.setAlpha(qBound(48, static_cast<int>(baseGuide.alpha() * 1.10), 255));

        const qreal axisStep = 360.0 / static_cast<qreal>(segments);
        const int oppositeMainIndex = segments / 2;
        for (int i = 0; i < segments; ++i) {
            const qreal angle = m_symmetryRotationDegrees + axisStep * i;
            const qreal radians = angle * 3.14159265358979323846 / 180.0;
            const QPointF axisDir(std::cos(radians), std::sin(radians));
            const QPointF axisEndCanvas = centerCanvas + axisDir * farRadius;

            if (i == 0 || i == oppositeMainIndex) {
                painter.setPen(QPen(primaryAxisColor, 1.8, Qt::SolidLine, Qt::RoundCap));
            } else {
                painter.setPen(QPen(secondaryAxisColor, 1.2, Qt::DashLine, Qt::RoundCap));
            }
            painter.drawLine(centerArt, canvasToArtPointUnclamped(axisEndCanvas));
        }

        const qreal sx = qMax(1.0, artRect.width() - 1.0)
                         / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
        const qreal sy = qMax(1.0, artRect.height() - 1.0)
                         / static_cast<qreal>(qMax(1, m_documentSize.height() - 1));

        if (!m_symmetryTransformLocked) {
            const QPointF rotateHandleArt = canvasToArtPoint(symmetryRotationHandleCanvasPoint());
            painter.setPen(QPen(linkColor, 1.3));
            painter.drawLine(centerArt, rotateHandleArt);

            painter.setBrush(centerFillColor);
            painter.setPen(QPen(centerStrokeColor, 1.2));
            painter.drawEllipse(centerArt, 7.0 * sx, 7.0 * sy);
            painter.drawLine(QPointF(centerArt.x() - 9.0 * sx, centerArt.y()), QPointF(centerArt.x() + 9.0 * sx, centerArt.y()));
            painter.drawLine(QPointF(centerArt.x(), centerArt.y() - 9.0 * sy), QPointF(centerArt.x(), centerArt.y() + 9.0 * sy));

            painter.setBrush(handleFillColor);
            painter.setPen(QPen(handleStrokeColor, 1.2));
            painter.drawEllipse(rotateHandleArt, 6.0 * sx, 6.0 * sy);
        }
        painter.restore();
    }

    // Draw the canvas frame before the selection so a full-canvas selection
    // remains visible instead of being covered by the blue outline.
    painter.setPen(QPen(m_outlineOuterColor, 1));
    painter.drawRect(artRect.adjusted(0, 0, -1, -1));
    painter.setPen(QPen(m_outlineInnerColor, 1));
    painter.drawRect(artRect.adjusted(1, 1, -2, -2));

    QPen antsLight(QColor(255, 255, 255, 240), 1.0, Qt::CustomDashLine);
    antsLight.setDashPattern({4.0, 4.0});
    antsLight.setDashOffset(m_selectionAntsDashOffset);
    QPen antsDark(QColor(0, 0, 0, 230), 1.0, Qt::CustomDashLine);
    antsDark.setDashPattern({4.0, 4.0});
    antsDark.setDashOffset(std::fmod(m_selectionAntsDashOffset + 4.0, 8.0));

    painter.save();
    painter.setClipRect(artRect, Qt::IntersectClip);

    if (hasSelectionRegion()) {
        QTransform selectionTransform;
        selectionTransform.translate(artRect.left(), artRect.top());
        selectionTransform.scale(qMax(1, artRect.width() - 1) / static_cast<qreal>(qMax(1, m_documentSize.width() - 1)),
                                 qMax(1, artRect.height() - 1) / static_cast<qreal>(qMax(1, m_documentSize.height() - 1)));
        const QPainterPath selectionInArt = selectionTransform.map(m_selectionPathCanvas);

        if (!selectionInArt.isEmpty()) {
            painter.setBrush(Qt::NoBrush);
            painter.setPen(antsDark);
            painter.drawPath(selectionInArt);
            painter.setPen(antsLight);
            painter.drawPath(selectionInArt);
        }
    }

    if (m_selectionToolEnabled && isFreeTransformMode() && hasSelectionRegion()) {
        // Selection pixels stay canvas-clipped, but the transform controls must
        // remain visible and interactive in the surrounding workspace margin.
        painter.setClipping(false);
        if (!m_freeTransformSessionActive) {
            refreshFreeTransformSession();
        }
        if (m_freeTransformSessionActive) {
            QVector<QPointF> boxView = {
                freeTransformHandleWorldPoint(0, m_freeTransformScaleX, m_freeTransformScaleY, m_freeTransformRotationDegrees, m_freeTransformTranslationCanvas),
                freeTransformHandleWorldPoint(2, m_freeTransformScaleX, m_freeTransformScaleY, m_freeTransformRotationDegrees, m_freeTransformTranslationCanvas),
                freeTransformHandleWorldPoint(4, m_freeTransformScaleX, m_freeTransformScaleY, m_freeTransformRotationDegrees, m_freeTransformTranslationCanvas),
                freeTransformHandleWorldPoint(6, m_freeTransformScaleX, m_freeTransformScaleY, m_freeTransformRotationDegrees, m_freeTransformTranslationCanvas)
            };

            QVector<QPointF> boxCanvas;
            boxCanvas.reserve(boxView.size());
            for (const QPointF &v : boxView) {
                boxCanvas.push_back(viewAlignedToCanvasPoint(v));
            }

            QPainterPath boxPath;
            boxPath.moveTo(canvasToArtPointUnclamped(boxCanvas[0]));
            for (int i = 1; i < boxCanvas.size(); ++i) {
                boxPath.lineTo(canvasToArtPointUnclamped(boxCanvas[i]));
            }
            boxPath.closeSubpath();

            painter.setBrush(Qt::NoBrush);
            painter.setPen(QPen(QColor(18, 18, 18, 225), 3.0, Qt::SolidLine, Qt::SquareCap, Qt::MiterJoin));
            painter.drawPath(boxPath);
            painter.setPen(QPen(QColor(255, 255, 255, 220), 1.0, Qt::DashLine));
            painter.drawPath(boxPath);

            const QPointF topCenterArt = (canvasToArtPointUnclamped(boxCanvas[0])
                                          + canvasToArtPointUnclamped(boxCanvas[1])) * 0.5;
            const QPointF boxCenterArt = (canvasToArtPointUnclamped(boxCanvas[0])
                                          + canvasToArtPointUnclamped(boxCanvas[2])) * 0.5;
            QLineF rotationStem(boxCenterArt, topCenterArt);
            if (rotationStem.length() > 0.001) {
                rotationStem.setLength(rotationStem.length() + 34.0);
                const QPointF rotationHandleArt = rotationStem.p2();
                painter.setPen(QPen(QColor(235, 62, 62, 245), 2.0, Qt::SolidLine, Qt::RoundCap));
                painter.drawLine(topCenterArt, rotationHandleArt);
                painter.setBrush(QColor(244, 68, 68, 255));
                painter.setPen(QPen(QColor(65, 8, 8, 245), 1.5));
                painter.drawEllipse(rotationHandleArt, 6.0, 6.0);
            }

            const QVector<QPointF> handlesView = freeTransformHandlePoints();
            painter.setPen(QPen(QColor(12, 12, 12, 240), 1.0));
            painter.setBrush(QColor(255, 255, 255, 240));
            for (const QPointF &h : handlesView) {
                const QPointF hp = canvasToArtPointUnclamped(viewAlignedToCanvasPoint(h));
                painter.drawRect(QRectF(hp.x() - 5.0, hp.y() - 5.0, 10.0, 10.0));
            }

            const QPointF pivotArt = canvasToArtPointUnclamped(viewAlignedToCanvasPoint(
                freeTransformPivotWorldPoint(m_freeTransformTranslationCanvas)));
            painter.setBrush(QColor(255, 196, 64, 235));
            painter.setPen(QPen(QColor(28, 20, 6, 240), 1.2));
            painter.drawEllipse(pivotArt, 4.5, 4.5);
            painter.drawLine(QPointF(pivotArt.x() - 8.0, pivotArt.y()), QPointF(pivotArt.x() + 8.0, pivotArt.y()));
            painter.drawLine(QPointF(pivotArt.x(), pivotArt.y() - 8.0), QPointF(pivotArt.x(), pivotArt.y() + 8.0));
        }
        painter.setClipRect(artRect, Qt::ReplaceClip);
    }

    if (m_selectionToolEnabled && !m_selectionWorkingPoints.isEmpty()) {
        QVector<QPointF> preview = m_selectionWorkingPoints;
        if (m_selectionToolMode == QStringLiteral("rect") && m_selectionDragActive) {
            const QVector<QPointF> viewPreview = {
                m_selectionStartCanvasPoint,
                QPointF(m_selectionPreviewCanvasPoint.x(), m_selectionStartCanvasPoint.y()),
                m_selectionPreviewCanvasPoint,
                QPointF(m_selectionStartCanvasPoint.x(), m_selectionPreviewCanvasPoint.y())
            };
            preview.clear();
            preview.reserve(viewPreview.size());
            for (const QPointF &vp : viewPreview) {
                preview.push_back(viewAlignedToCanvasPoint(vp));
            }
        } else if (m_selectionToolMode == QStringLiteral("polyline") && m_selectionPolylineBuilding) {
            preview.push_back(m_selectionPreviewCanvasPoint);
        }

        if (preview.size() >= 2) {
            QVector<QPointF> previewArt;
            previewArt.reserve(preview.size());
            for (const QPointF &p : preview) {
                previewArt.push_back(canvasToArtPoint(p));
            }

            bool closePreview = false;
            if (m_selectionToolMode == QStringLiteral("rect")) {
                closePreview = previewArt.size() >= 4;
            } else if (m_selectionToolMode == QStringLiteral("lasso")) {
                closePreview = previewArt.size() >= 3;
            } else if (m_selectionToolMode == QStringLiteral("polyline")) {
                closePreview = previewArt.size() >= 3
                               && QLineF(previewArt.front(), previewArt.back()).length() <= 10.0;
            }

            if (closePreview) {
                QPainterPath previewFillPath;
                previewFillPath.moveTo(previewArt.front());
                for (int i = 1; i < previewArt.size(); ++i) {
                    previewFillPath.lineTo(previewArt[i]);
                }
                previewFillPath.closeSubpath();
                painter.fillPath(previewFillPath, QColor(255, 255, 255, 36));

                painter.setBrush(Qt::NoBrush);
                painter.setPen(antsDark);
                painter.drawPath(previewFillPath);
                painter.setPen(antsLight);
                painter.drawPath(previewFillPath);
            } else {
                painter.setBrush(Qt::NoBrush);
                painter.setPen(antsDark);
                for (int i = 1; i < previewArt.size(); ++i) {
                    painter.drawLine(previewArt[i - 1], previewArt[i]);
                }
                painter.setPen(antsLight);
                for (int i = 1; i < previewArt.size(); ++i) {
                    painter.drawLine(previewArt[i - 1], previewArt[i]);
                }
            }

            if (m_selectionToolMode == QStringLiteral("polyline") && !previewArt.isEmpty()) {
                const bool hasMovingPreviewPoint = previewArt.size() > m_selectionWorkingPoints.size();
                const bool nearClose = hasMovingPreviewPoint
                                       && previewArt.size() >= 3
                                       && QLineF(previewArt.front(), previewArt.back()).length() <= 10.0;

                painter.setPen(QPen(QColor(0, 0, 0, 220), 1.0));
                painter.setBrush(QColor(255, 255, 255, 220));
                for (int i = 0; i < previewArt.size() - 1; ++i) {
                    painter.drawEllipse(previewArt[i], 2.6, 2.6);
                }

                if (previewArt.size() >= 2 && hasMovingPreviewPoint) {
                    painter.setPen(nearClose ? antsLight : antsDark);
                    painter.drawLine(previewArt.back(), previewArt.front());
                }

                if (previewArt.size() >= 2) {
                    painter.setBrush(nearClose ? QColor(255, 255, 255, 66) : Qt::NoBrush);
                    painter.setPen(QPen(nearClose ? QColor(255, 255, 255, 250) : QColor(0, 0, 0, 210),
                                        nearClose ? 2.0 : 1.2));
                    painter.drawEllipse(previewArt.front(), nearClose ? 7.0 : 5.2, nearClose ? 7.0 : 5.2);
                }

                painter.setBrush(QColor(255, 255, 255, 250));
                painter.setPen(QPen(QColor(20, 20, 20, 245), 1.0));
                painter.drawEllipse(previewArt.back(), 3.3, 3.3);
            }

            if (m_selectionToolMode == QStringLiteral("lasso")
                && m_selectionDragActive
                && !previewArt.isEmpty()) {
                const qreal snapRadiusCanvas = 8.0;
                const qreal scaleX = qMax(1.0, artRect.width() - 1.0)
                                     / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
                const qreal scaleY = qMax(1.0, artRect.height() - 1.0)
                                     / static_cast<qreal>(qMax(1, m_documentSize.height() - 1));
                const qreal radiusX = snapRadiusCanvas * scaleX;
                const qreal radiusY = snapRadiusCanvas * scaleY;
                const bool nearClose = preview.size() >= 3
                                       && QLineF(preview.front(), preview.back()).length() <= snapRadiusCanvas;

                painter.setBrush(nearClose ? QColor(255, 255, 255, 32) : Qt::NoBrush);
                painter.setPen(QPen(nearClose ? QColor(255, 255, 255, 235) : QColor(255, 255, 255, 145),
                                    nearClose ? 1.8 : 1.2,
                                    Qt::DashLine));
                painter.drawEllipse(previewArt.front(), radiusX, radiusY);
            }
        }
    }

    if (m_selectedTextLayerIndex >= 0 && m_selectedTextElementIndex >= 0) {
        const QRectF bounds = textElementBounds(m_selectedTextLayerIndex, m_selectedTextElementIndex);
        if (!bounds.isEmpty()) {
            const QRectF handleRect = QRectF(canvasToArtPoint(bounds.topLeft()),
                                             canvasToArtPoint(bounds.bottomRight())).normalized();
            painter.setBrush(Qt::NoBrush);
            painter.setPen(QPen(QColor(76, 180, 255, 235), 1.5, Qt::DashLine));
            painter.drawRect(handleRect);
            painter.setBrush(QColor(76, 180, 255, 245));
            painter.setPen(QPen(Qt::white, 1.0));
            const qreal hs = 5.0;
            for (const QPointF &point : {handleRect.topLeft(), handleRect.topRight(),
                                         handleRect.bottomLeft(), handleRect.bottomRight()}) {
                painter.drawRect(QRectF(point.x() - hs, point.y() - hs, hs * 2.0, hs * 2.0));
            }
            const QPointF rotateHandle(handleRect.center().x(), handleRect.top() - 24.0);
            painter.drawLine(QPointF(handleRect.center().x(), handleRect.top()), rotateHandle);
            painter.drawEllipse(rotateHandle, hs + 1.0, hs + 1.0);
        }
    }

    painter.restore();

    painter.restore();

    if (m_quickAdjustMode != QuickAdjustMode::None) {
        const QPointF center = m_tilingPreviewEnabled
                                   ? m_quickAdjustAnchorWidgetPoint
                                   : canvasToWidgetPoint(m_quickAdjustAnchorCanvasPoint);
        const qreal radiusCanvasX = (m_quickAdjustMode == QuickAdjustMode::BrushSize)
                                        ? qMax(0.5, m_quickAdjustPreviewValue * 0.5)
                                        : qMax(64.0,
                                               qMin(m_documentSize.width(), m_documentSize.height())
                                                   * 0.08);
        const qreal radiusCanvasY = qMax(0.5, radiusCanvasX * (m_roundnessPercent / 100.0));
        const qreal sx = qMax(1, artRect.width() - 1) / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
        const qreal sy = qMax(1, artRect.height() - 1) / static_cast<qreal>(qMax(1, m_documentSize.height() - 1));
        // Size adjustment uses radial screen distance, so its indicator must
        // use the same circular radius as the anchor and inverse conversion.
        const qreal sizeRadius = radiusCanvasX / ((1.0 / sx + 1.0 / sy) * 0.5);
        const qreal radiusWidgetX = m_quickAdjustMode == QuickAdjustMode::BrushSize
                                       ? sizeRadius : radiusCanvasX * sx;
        const qreal radiusWidgetY = m_quickAdjustMode == QuickAdjustMode::BrushSize
                                       ? sizeRadius : radiusCanvasY * sy;

        painter.save();
        painter.setRenderHint(QPainter::Antialiasing, true);
        painter.translate(center);
        painter.rotate(m_angleDegrees + m_viewRotationDegrees);
        if (m_quickAdjustMode == QuickAdjustMode::BrushOpacity) {
            QColor fill = m_brushInkColor;
            fill.setAlpha(qBound(0, static_cast<int>(std::lround((m_quickAdjustPreviewValue / 100.0) * 255.0)), 255));
            painter.setBrush(fill);
        } else {
            painter.setBrush(QColor(0, 0, 0, 30));
        }
        painter.setPen(QPen(QColor(0, 0, 0, 220), 1.6));
        painter.drawEllipse(QRectF(-radiusWidgetX, -radiusWidgetY, radiusWidgetX * 2.0, radiusWidgetY * 2.0));
        painter.setBrush(Qt::NoBrush);
        painter.setPen(QPen(QColor(245, 252, 247, 245), 1.1));
        painter.drawEllipse(QRectF(-radiusWidgetX, -radiusWidgetY, radiusWidgetX * 2.0, radiusWidgetY * 2.0));
        painter.restore();

        const QString label = (m_quickAdjustMode == QuickAdjustMode::BrushSize)
                                  ? L("quick_adjust.size", "Size %1 px").arg(m_quickAdjustPreviewValue)
                                  : L("quick_adjust.opacity", "Opacity %1%").arg(m_quickAdjustPreviewValue);
        const QRect textRect = QRect(center.toPoint() + QPoint(14, 14), QSize(128, 26));
        painter.save();
        painter.setPen(QColor(245, 252, 247, 245));
        painter.fillRect(textRect.adjusted(-6, -4, 6, 4), QColor(0, 0, 0, 130));
        painter.drawText(textRect, Qt::AlignLeft | Qt::AlignVCenter, label);
        painter.restore();
    } else if (m_showBrushCursor) {
        const QPointF center = m_tilingPreviewEnabled
                                   ? m_brushCursorWidgetPoint
                                   : canvasToWidgetPoint(m_brushCursorCanvasPoint);
        const qreal radiusCanvasX = brushPreviewRadiusPx(m_brushCursorPressure);
        const qreal radiusCanvasY = qMax(0.5, radiusCanvasX * (m_roundnessPercent / 100.0));
        const qreal sx = qMax(1, artRect.width() - 1) / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
        const qreal sy = qMax(1, artRect.height() - 1) / static_cast<qreal>(qMax(1, m_documentSize.height() - 1));
        const qreal radiusWidgetX = radiusCanvasX * sx;
        const qreal radiusWidgetY = radiusCanvasY * sy;

        painter.save();
        painter.setRenderHint(QPainter::Antialiasing, true);
        painter.translate(center);
        painter.rotate(m_angleDegrees + m_viewRotationDegrees);
        painter.setBrush(Qt::NoBrush);
        painter.setPen(QPen(QColor(5, 10, 10, 220), 1.6));
        painter.drawEllipse(QRectF(-radiusWidgetX, -radiusWidgetY, radiusWidgetX * 2.0, radiusWidgetY * 2.0));
        painter.setPen(QPen(QColor(238, 246, 240, 235), 1.0));
        painter.drawEllipse(QRectF(-radiusWidgetX, -radiusWidgetY, radiusWidgetX * 2.0, radiusWidgetY * 2.0));
        painter.restore();
    }

    if (m_straightStrokeActive && m_straightStrokeDragged) {
        const QPointF from = canvasToWidgetPoint(m_straightStrokeStartPoint);
        const QPointF to = canvasToWidgetPoint(m_straightStrokeEndPoint);
        const qreal radius = brushPreviewRadiusPx(m_straightStrokeEndPressure);
        const qreal scale = qMax(1, artRect.width() - 1)
                            / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
        painter.save();
        painter.setRenderHint(QPainter::Antialiasing, true);
        QColor preview = m_tool == Tool::Brush ? m_brushInkColor : QColor(255, 255, 255, 180);
        preview.setAlpha(qMax(80, preview.alpha()));
        painter.setPen(QPen(preview, qMax(1.0, radius * 2.0 * scale), Qt::SolidLine, Qt::RoundCap));
        painter.drawLine(from, to);
        painter.restore();
    }

    if (m_colorPickerPreviewActive) {
        const QColor swatchColor = m_colorPickerPreviewValid
                                       ? m_colorPickerPreviewHoverColor
                                       : QColor(0, 0, 0, 0);

        const QSize swatchSize(28, 28);
        const int totalW = swatchSize.width();
        const int totalH = swatchSize.height();

        // Default to the cursor's upper-left. For a tablet, use the side
        // opposite the pen lean so the hand does not cover the sampled colour.
        QPoint topLeft = m_colorPickerPreviewWidgetPoint.toPoint() - QPoint(totalW + 14, totalH + 14);
        const qreal tiltLength = std::hypot(m_colorPickerPreviewTabletTilt.x(),
                                            m_colorPickerPreviewTabletTilt.y());
        if (m_colorPickerPreviewTabletInput && tiltLength > 0.5) {
            const QPointF opposite = -m_colorPickerPreviewTabletTilt / tiltLength;
            const QPointF center = m_colorPickerPreviewWidgetPoint + opposite * (qMax(totalW, totalH) + 16.0);
            topLeft = (center - QPointF(totalW * 0.5, totalH * 0.5)).toPoint();
        }
        if (topLeft.x() + totalW > width() - 2) {
            topLeft.setX(width() - totalW - 2);
        }
        if (topLeft.y() + totalH > height() - 2) {
            topLeft.setY(height() - totalH - 2);
        }
        topLeft.setX(qMax(2, topLeft.x()));
        topLeft.setY(qMax(2, topLeft.y()));

        const QRect swatchRect(topLeft, swatchSize);

        painter.save();
        painter.setRenderHint(QPainter::Antialiasing, false);

        if (swatchColor.alpha() < 255) {
            const int checker = 6;
            const QColor c0(208, 208, 208, 255);
            const QColor c1(152, 152, 152, 255);
            for (int y = swatchRect.top(); y <= swatchRect.bottom(); y += checker) {
                for (int x = swatchRect.left(); x <= swatchRect.right(); x += checker) {
                    const bool even = (((x - swatchRect.left()) / checker) + ((y - swatchRect.top()) / checker)) % 2 == 0;
                    painter.fillRect(QRect(x,
                                           y,
                                           qMin(checker, swatchRect.right() - x + 1),
                                           qMin(checker, swatchRect.bottom() - y + 1)),
                                    even ? c0 : c1);
                }
            }
        }

        painter.fillRect(swatchRect, swatchColor);

        painter.setPen(QPen(QColor(255, 255, 255, 255), 1.0));
        painter.setBrush(Qt::NoBrush);
        painter.drawRect(swatchRect.adjusted(0, 0, -1, -1));

        if (!m_colorPickerPreviewValid) {
            painter.setPen(QPen(QColor(255, 128, 128, 240), 1.5));
            painter.drawLine(swatchRect.topLeft() + QPoint(2, 2), swatchRect.bottomRight() - QPoint(2, 2));
            painter.drawLine(swatchRect.topRight() + QPoint(-2, 2), swatchRect.bottomLeft() + QPoint(2, -2));
        }
        painter.restore();
    }
}

void DrawingCanvas::resizeEvent(QResizeEvent *event)
{
    QWidget::resizeEvent(event);
    update();
}

void DrawingCanvas::enterEvent(QEnterEvent *event)
{
    QWidget::enterEvent(event);
    if (updateSymmetryHandleCursor(event->position())) {
        return;
    }
    if (!updateColorPickerPreviewFromWidgetPoint(event->position(), QApplication::keyboardModifiers(), true)) {
        applySystemCursorForBrushCursor(true);
    }
    if (m_selectionToolEnabled) {
        updateSelectionInteractionCursor(event->position(), QApplication::keyboardModifiers());
    }
}

void DrawingCanvas::leaveEvent(QEvent *event)
{
    QWidget::leaveEvent(event);
    updateColorPickerPreviewFromWidgetPoint(QPointF(), Qt::NoModifier, false);
    if (m_showBrushCursor) {
        setBrushCursorVisible(false);
        update();
    } else {
        applySystemCursorForBrushCursor(true);
    }
}

void DrawingCanvas::focusInEvent(QFocusEvent *event)
{
    QWidget::focusInEvent(event);
    const QPoint localPos = mapFromGlobal(QCursor::pos());
    if (!updateColorPickerPreviewFromWidgetPoint(QPointF(localPos), QApplication::keyboardModifiers(), true)) {
        applySystemCursorForBrushCursor(true);
    }
    if (m_selectionToolEnabled) {
        updateSelectionInteractionCursor(QPointF(localPos), QApplication::keyboardModifiers());
    }
}

void DrawingCanvas::focusOutEvent(QFocusEvent *event)
{
    QWidget::focusOutEvent(event);
    updateColorPickerPreviewFromWidgetPoint(QPointF(), Qt::NoModifier, false);
    if (m_showBrushCursor) {
        setBrushCursorVisible(false);
        update();
    } else {
        applySystemCursorForBrushCursor(true);
    }
}

void DrawingCanvas::keyPressEvent(QKeyEvent *event)
{
    const QPoint localPos = mapFromGlobal(QCursor::pos());
    updateColorPickerPreviewFromWidgetPoint(QPointF(localPos), event->modifiers(), true);

    if (event->key() == Qt::Key_Escape && m_quickAdjustMode != QuickAdjustMode::None) {
        cancelQuickAdjust();
        event->accept();
        return;
    }

    if (m_quickAdjustEnabled
        && !m_selectionToolEnabled
        && !event->isAutoRepeat()
        && event->key() == Qt::Key_F
        && m_quickAdjustMode == QuickAdjustMode::None) {
        beginQuickAdjust(event->modifiers().testFlag(Qt::ShiftModifier)
                             ? QuickAdjustMode::BrushOpacity
                             : QuickAdjustMode::BrushSize);
        event->accept();
        return;
    }

    if (event->key() == Qt::Key_Escape && m_layerTranslationActive) {
        endLayerTranslation(false);
        event->accept();
        return;
    }

    if (!m_selectionToolEnabled) {
        QWidget::keyPressEvent(event);
        return;
    }

    if (isFreeTransformMode()) {
        if (event->key() == Qt::Key_Return || event->key() == Qt::Key_Enter) {
            finalizeFreeTransform(true);
            event->accept();
            return;
        }

        if (event->key() == Qt::Key_Escape) {
            finalizeFreeTransform(false);
            event->accept();
            return;
        }
    }

    if (event->key() == Qt::Key_Escape) {
        if (m_selectionTranslationActive) {
            endSelectionTranslation(false);
            event->accept();
            return;
        }

        if (m_selectionPolylineBuilding || m_selectionDragActive) {
            cancelSelectionConstruction();
            event->accept();
            return;
        }
    }

    QWidget::keyPressEvent(event);
}

void DrawingCanvas::keyReleaseEvent(QKeyEvent *event)
{
    const QPoint localPos = mapFromGlobal(QCursor::pos());
    updateColorPickerPreviewFromWidgetPoint(QPointF(localPos), QApplication::keyboardModifiers(), true);
    QWidget::keyReleaseEvent(event);
}

void DrawingCanvas::mousePressEvent(QMouseEvent *event)
{
    if (m_quickAdjustMode != QuickAdjustMode::None) {
        if (event->button() == Qt::LeftButton) {
            updateQuickAdjustFromWidgetPoint(event->position());
            commitQuickAdjust();
        } else if (event->button() == Qt::RightButton) {
            cancelQuickAdjust();
        }
        event->accept();
        return;
    }

    if (event->button() == Qt::LeftButton) {
        setFocus(Qt::MouseFocusReason);
    }

    if (m_selectionToolEnabled) {
        forceHideBrushCursor();
        updateSelectionInteractionCursor(event->position(), event->modifiers());

        if (isFreeTransformMode()) {
            if (!hasSelectionRegion()) {
                ensureSelectionForFreeTransform();
            }
            if (!hasSelectionRegion()) {
                event->accept();
                return;
            }
            if (!m_freeTransformSessionActive) {
                refreshFreeTransformSession();
            }
            if (event->button() == Qt::RightButton && selectionCanvasContainsWidgetPoint(event->position())) {
                const QPointF canvasPoint = widgetToCanvasPoint(event->position());
                const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);
                const bool inTransformArea = freeTransformPointInside(viewPoint)
                                             || freeTransformHandleAt(viewPoint) >= 0
                                             || freeTransformPointNearRotationRing(viewPoint)
                                             || freeTransformPointNearPivot(viewPoint);
                if (inTransformArea && m_freeTransformSessionActive) {
                    if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
                        endFreeTransformInteraction(true);
                    }

                    QMenu menu(this);
                    QAction *flipHorizontalAction = menu.addAction(L("transform.flip_horizontal", "수평 뒤집기"));
                    QAction *flipVerticalAction = menu.addAction(L("transform.flip_vertical", "수직 뒤집기"));
                    QAction *picked = menu.exec(event->globalPosition().toPoint());

                    if (picked == flipHorizontalAction || picked == flipVerticalAction) {
                        ensureFreeTransformUndoState();
                        if (picked == flipHorizontalAction) {
                            m_freeTransformScaleX = -m_freeTransformScaleX;
                        } else {
                            m_freeTransformScaleY = -m_freeTransformScaleY;
                        }
                        applyFreeTransformPreview();
                        if (onLayerStackChanged) {
                            onLayerStackChanged();
                        }
                    }

                    event->accept();
                    return;
                }
            }
            if (event->button() == Qt::LeftButton) {
                beginFreeTransformInteraction(widgetToCanvasPoint(event->position()), event->modifiers());
                updateSelectionInteractionCursor(event->position(), event->modifiers());
            }
            event->accept();
            return;
        }

        if (event->button() == Qt::RightButton && m_selectionToolMode == QStringLiteral("polyline") && m_selectionPolylineBuilding) {
            if (!m_selectionWorkingPoints.isEmpty()) {
                m_selectionWorkingPoints.removeLast();
            }
            if (m_selectionWorkingPoints.isEmpty()) {
                m_selectionPolylineBuilding = false;
            }
            updateSelectionAntsAnimationState();
            update();
            event->accept();
            return;
        }

        if (event->button() == Qt::LeftButton && selectionCanvasContainsWidgetPoint(event->position())) {
            const QPointF canvasPoint = widgetToCanvasPoint(event->position());
            if (!m_selectionPolylineBuilding && hasSelectionRegion()) {
                const bool movePixels = event->modifiers().testFlag(Qt::ControlModifier)
                                        && !event->modifiers().testFlag(Qt::ShiftModifier)
                                        && !event->modifiers().testFlag(Qt::AltModifier);
                const bool canStartSelectionMove = movePixels
                                                       ? m_selectionClipRegion.contains(canvasPoint.toPoint())
                                                       : isNearSelectionBoundary(canvasPoint);
                if (canStartSelectionMove && (!movePixels || canMoveSelectionPixels())) {
                    beginSelectionTranslation(canvasPoint, movePixels);
                    updateSelectionInteractionCursor(event->position(), event->modifiers());
                    event->accept();
                    return;
                }
            }

            if (m_selectionToolMode == QStringLiteral("polyline")) {
                if (!m_selectionPolylineBuilding) {
                    m_selectionPolylineBuilding = true;
                    m_selectionWorkingPoints.clear();
                    m_selectionPendingCombineMode = selectionCombineModeForModifiers(event->modifiers());
                }
                if (!m_selectionWorkingPoints.isEmpty()
                    && m_selectionWorkingPoints.size() >= 3
                    && QLineF(m_selectionWorkingPoints.front(), canvasPoint).length() <= 6.0) {
                    applySelectionPolygon(m_selectionWorkingPoints, m_selectionPendingCombineMode);
                    m_selectionPolylineBuilding = false;
                    m_selectionWorkingPoints.clear();
                } else {
                    m_selectionWorkingPoints.push_back(canvasPoint);
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
            } else {
                m_selectionDragActive = true;
                m_selectionPendingCombineMode = selectionCombineModeForModifiers(event->modifiers());
                if (m_selectionToolMode == QStringLiteral("rect")) {
                    const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);
                    m_selectionStartCanvasPoint = viewPoint;
                    m_selectionPreviewCanvasPoint = viewPoint;
                } else {
                    m_selectionStartCanvasPoint = canvasPoint;
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
                m_selectionWorkingPoints.clear();
                m_selectionWorkingPoints.push_back(canvasPoint);
            }
            updateSelectionAntsAnimationState();
            update();
            event->accept();
            return;
        }
        event->accept();
        return;
    }

    const bool insideCanvas = canvasRect().contains(event->position().toPoint());
    const QPointF canvasPoint = widgetToCanvasPoint(event->position());
    if (event->button() == Qt::LeftButton) {
        updateColorPickerPreviewFromWidgetPoint(event->position(), event->modifiers(), true);
    }
    if (event->button() == Qt::LeftButton && insideCanvas
        && tryHandleModifierColorSample(canvasPoint, event->modifiers())) {
        updateColorPickerPreviewFromWidgetPoint(event->position(), event->modifiers(), true);
        event->accept();
        return;
    }

    if (event->button() == Qt::LeftButton && insideCanvas && m_symmetryEnabled) {
        const SymmetryHandleDragMode handleMode = symmetryHandleAtCanvasPoint(canvasPoint);
        if (handleMode != SymmetryHandleDragMode::None) {
            beginSymmetryHandleDrag(handleMode, canvasPoint);
            event->accept();
            return;
        }
    }

    setBrushCursorFromWidgetPoint(event->position(), 1.0);
    if (event->button() == Qt::LeftButton && insideCanvas) {
        if (event->modifiers().testFlag(Qt::ControlModifier)
            && !event->modifiers().testFlag(Qt::ShiftModifier)
            && !event->modifiers().testFlag(Qt::AltModifier)) {
            if (hasSelectionRegion()) {
                if (m_selectionClipRegion.contains(canvasPoint.toPoint()) && canMoveSelectionPixels()) {
                    beginSelectionTranslation(canvasPoint, true);
                    event->accept();
                    return;
                }
            } else if (canMoveActiveLayerPixels()) {
                beginLayerTranslation(canvasPoint);
                event->accept();
                return;
            }
        }
        m_straightStrokeActive = event->modifiers().testFlag(Qt::ShiftModifier);
        m_straightStrokeDragged = false;
        m_straightStrokeStartPoint = canvasPoint;
        m_straightStrokeStartWidgetPoint = event->position();
        m_straightStrokeEndPoint = canvasPoint;
        m_straightStrokeEndPressure = 1.0;
        if (!m_straightStrokeActive) {
            beginStroke(canvasPoint, 1.0);
        }
    }
}

void DrawingCanvas::mouseMoveEvent(QMouseEvent *event)
{
    if (m_quickAdjustMode != QuickAdjustMode::None) {
        updateQuickAdjustFromWidgetPoint(event->position());
        event->accept();
        return;
    }

    if (m_selectionToolEnabled) {
        QPointF selectionPosition = event->position();
        const bool activeSelectionDrag = m_selectionDragActive
                                         || m_selectionTranslationActive
                                         || m_freeTransformInteractionMode != FreeTransformInteractionMode::None;
        if (activeSelectionDrag && (event->buttons() & Qt::LeftButton) && onSelectionDragAutoScroll) {
            onSelectionDragAutoScroll(event->globalPosition().toPoint());
            selectionPosition = QPointF(mapFromGlobal(event->globalPosition().toPoint()));
        }
        updateSelectionInteractionCursor(selectionPosition, event->modifiers());
        if (isFreeTransformMode()) {
            if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
                updateFreeTransformInteraction(widgetToCanvasPoint(selectionPosition), event->modifiers());
                updateSelectionInteractionCursor(selectionPosition, event->modifiers());
                event->accept();
                return;
            }
            event->accept();
            return;
        }

        if (m_selectionTranslationActive) {
            updateSelectionTranslation(widgetToCanvasPoint(selectionPosition));
            updateSelectionInteractionCursor(selectionPosition, event->modifiers());
            event->accept();
            return;
        }

        if (m_selectionToolMode == QStringLiteral("polyline")) {
            if (m_selectionPolylineBuilding) {
                m_selectionPreviewCanvasPoint = widgetToCanvasPoint(selectionPosition);
                update();
            }
            event->accept();
            return;
        }

        if (m_selectionDragActive) {
            QPointF canvasPoint = widgetToCanvasPoint(selectionPosition);
            if (m_selectionToolMode == QStringLiteral("rect")) {
                m_selectionPreviewCanvasPoint = canvasToViewAlignedPoint(canvasPoint);
            } else {
                m_selectionPreviewCanvasPoint = canvasPoint;
            }
            if (m_selectionToolMode == QStringLiteral("lasso")) {
                if (!m_selectionWorkingPoints.isEmpty()
                    && m_selectionWorkingPoints.size() >= 3
                    && QLineF(m_selectionWorkingPoints.front(), canvasPoint).length() <= 8.0) {
                    canvasPoint = m_selectionWorkingPoints.front();
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
                if (m_selectionWorkingPoints.isEmpty()
                    || QLineF(m_selectionWorkingPoints.back(), canvasPoint).length() >= 1.2) {
                    m_selectionWorkingPoints.push_back(canvasPoint);
                }
            }
            update();
        }
        event->accept();
        return;
    }

    if (m_symmetryHandleDragMode != SymmetryHandleDragMode::None) {
        updateSymmetryHandleCursor(event->position());
        updateSymmetryHandleDrag(widgetToCanvasPoint(event->position()));
        event->accept();
        return;
    }

    if (m_selectionTranslationActive) {
        updateSelectionTranslation(widgetToCanvasPoint(event->position()));
        event->accept();
        return;
    }

    if (m_layerTranslationActive) {
        updateLayerTranslation(widgetToCanvasPoint(event->position()));
        event->accept();
        return;
    }

    if (updateColorPickerPreviewFromWidgetPoint(event->position(), event->modifiers(), true)) {
        event->accept();
        return;
    }

    if (updateSymmetryHandleCursor(event->position())) {
        event->accept();
        return;
    }

    setBrushCursorFromWidgetPoint(event->position(), 1.0);
    if (event->buttons() & Qt::LeftButton) {
        if (m_straightStrokeActive) {
            m_straightStrokeEndPoint = widgetToCanvasPoint(event->position());
            m_straightStrokeEndPressure = 1.0;
            if (QLineF(m_straightStrokeStartWidgetPoint, event->position()).length() >= 3.0) {
                m_straightStrokeDragged = true;
            }
            update();
        } else if (m_isDrawing) {
            continueStroke(widgetToCanvasPoint(event->position()), 1.0);
        }
    }
}

void DrawingCanvas::mouseReleaseEvent(QMouseEvent *event)
{
    if (m_quickAdjustMode != QuickAdjustMode::None) {
        event->accept();
        return;
    }

    if (m_selectionToolEnabled) {
        if (isFreeTransformMode()) {
            if (event->button() == Qt::LeftButton
                && m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
                endFreeTransformInteraction(true);
            }
            updateSelectionInteractionCursor(event->position(), event->modifiers());
            event->accept();
            return;
        }

        if (event->button() == Qt::LeftButton && m_selectionTranslationActive) {
            endSelectionTranslation(true);
            updateSelectionInteractionCursor(event->position(), event->modifiers());
            event->accept();
            return;
        }

        if (event->button() == Qt::LeftButton && m_selectionDragActive) {
            if (m_selectionToolMode == QStringLiteral("rect")) {
                const QPointF a = m_selectionStartCanvasPoint;
                const QPointF b = m_selectionPreviewCanvasPoint;
                const QVector<QPointF> viewPoly = {
                    QPointF(qMin(a.x(), b.x()), qMin(a.y(), b.y())),
                    QPointF(qMax(a.x(), b.x()), qMin(a.y(), b.y())),
                    QPointF(qMax(a.x(), b.x()), qMax(a.y(), b.y())),
                    QPointF(qMin(a.x(), b.x()), qMax(a.y(), b.y()))
                };
                QVector<QPointF> poly;
                poly.reserve(viewPoly.size());
                for (const QPointF &vp : viewPoly) {
                    poly.push_back(viewAlignedToCanvasPoint(vp));
                }
                applySelectionPolygon(poly, m_selectionPendingCombineMode);
            } else if (m_selectionToolMode == QStringLiteral("lasso")) {
                if (m_selectionWorkingPoints.size() >= 3
                    && QLineF(m_selectionWorkingPoints.front(), m_selectionWorkingPoints.back()).length() <= 8.0) {
                    m_selectionWorkingPoints.back() = m_selectionWorkingPoints.front();
                }
                applySelectionPolygon(m_selectionWorkingPoints, m_selectionPendingCombineMode);
            }
            m_selectionDragActive = false;
            m_selectionWorkingPoints.clear();
            update();
        }
        updateSelectionInteractionCursor(event->position(), event->modifiers());
        event->accept();
        return;
    }

    if (event->button() == Qt::LeftButton && m_symmetryHandleDragMode != SymmetryHandleDragMode::None) {
        endSymmetryHandleDrag();
        event->accept();
        return;
    }

    if (event->button() == Qt::LeftButton && m_selectionTranslationActive) {
        endSelectionTranslation(true);
        event->accept();
        return;
    }

    if (event->button() == Qt::LeftButton && m_layerTranslationActive) {
        endLayerTranslation(true);
        event->accept();
        return;
    }

    const bool pickerPreviewActive = updateColorPickerPreviewFromWidgetPoint(event->position(), event->modifiers(), true);

    if (pickerPreviewActive) {
        if (event->button() == Qt::LeftButton) {
            endStroke();
        }
        event->accept();
        return;
    }

    setBrushCursorFromWidgetPoint(event->position(), 1.0);
    if (event->button() == Qt::LeftButton) {
        if (m_straightStrokeActive) {
            m_straightStrokeEndPoint = widgetToCanvasPoint(event->position());
            beginStroke(m_straightStrokeStartPoint, m_straightStrokeEndPressure);
            continueStroke(m_straightStrokeEndPoint, m_straightStrokeEndPressure);
        }
        endStroke();
        m_straightStrokeActive = false;
    }
}

void DrawingCanvas::mouseDoubleClickEvent(QMouseEvent *event)
{
    if (m_selectionToolEnabled
        && m_selectionToolMode == QStringLiteral("polyline")
        && event->button() == Qt::LeftButton
        && m_selectionPolylineBuilding) {
        QVector<QPointF> poly = m_selectionWorkingPoints;
        const QPointF hitPoint = widgetToCanvasPoint(event->position());
        if (poly.isEmpty() || QLineF(poly.back(), hitPoint).length() > 0.8) {
            poly.push_back(hitPoint);
        }
        applySelectionPolygon(poly, m_selectionPendingCombineMode);
        m_selectionPolylineBuilding = false;
        m_selectionWorkingPoints.clear();
        update();
        event->accept();
        return;
    }

    QWidget::mouseDoubleClickEvent(event);
}

void DrawingCanvas::tabletEvent(QTabletEvent *event)
{
    if (event->type() == QEvent::TabletPress || event->type() == QEvent::TabletMove) {
        m_colorPickerPreviewTabletTilt = QPointF(event->xTilt(), event->yTilt());
    }
    if (m_quickAdjustMode != QuickAdjustMode::None) {
        if (event->type() == QEvent::TabletMove || event->type() == QEvent::TabletPress) {
            updateQuickAdjustFromWidgetPoint(event->position());
        }
        if (event->type() == QEvent::TabletPress && event->button() == Qt::LeftButton) {
            commitQuickAdjust();
        } else if (event->type() == QEvent::TabletPress && event->button() == Qt::RightButton) {
            cancelQuickAdjust();
        }
        event->accept();
        return;
    }

    if (event->type() == QEvent::TabletPress) {
        setFocus(Qt::MouseFocusReason);
    }

    if (m_selectionToolEnabled) {
        forceHideBrushCursor();
        const bool insideCanvas = selectionCanvasContainsWidgetPoint(event->position());
        QPointF canvasPoint = widgetToCanvasPoint(event->position());
        const Qt::KeyboardModifiers modifiers = event->modifiers();

        if (isFreeTransformMode()) {
            if (!hasSelectionRegion()) {
                ensureSelectionForFreeTransform();
            }
            if (!hasSelectionRegion()) {
                event->accept();
                return;
            }
            if (!m_freeTransformSessionActive) {
                refreshFreeTransformSession();
            }

            switch (event->type()) {
            case QEvent::TabletPress:
                beginFreeTransformInteraction(canvasPoint, modifiers);
                break;
            case QEvent::TabletMove:
                if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
                    updateFreeTransformInteraction(canvasPoint, modifiers);
                }
                break;
            case QEvent::TabletRelease:
                if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
                    endFreeTransformInteraction(true);
                }
                break;
            default:
                break;
            }

            event->accept();
            return;
        }

        if (event->button() == Qt::RightButton
            && event->type() == QEvent::TabletPress
            && m_selectionToolMode == QStringLiteral("polyline")
            && m_selectionPolylineBuilding) {
            if (!m_selectionWorkingPoints.isEmpty()) {
                m_selectionWorkingPoints.removeLast();
            }
            if (m_selectionWorkingPoints.isEmpty()) {
                m_selectionPolylineBuilding = false;
            }
            updateSelectionAntsAnimationState();
            update();
            event->accept();
            return;
        }

        switch (event->type()) {
        case QEvent::TabletPress:
            if (!insideCanvas) {
                event->accept();
                return;
            }

            if (!m_selectionPolylineBuilding && hasSelectionRegion()) {
                const bool movePixels = modifiers.testFlag(Qt::ControlModifier)
                                        && !modifiers.testFlag(Qt::ShiftModifier)
                                        && !modifiers.testFlag(Qt::AltModifier);
                const bool canStartSelectionMove = movePixels
                                                       ? m_selectionClipRegion.contains(canvasPoint.toPoint())
                                                       : isNearSelectionBoundary(canvasPoint);
                if (canStartSelectionMove && (!movePixels || canMoveSelectionPixels())) {
                    beginSelectionTranslation(canvasPoint, movePixels);
                    event->accept();
                    return;
                }
            }

            if (m_selectionToolMode == QStringLiteral("polyline")) {
                if (!m_selectionPolylineBuilding) {
                    m_selectionPolylineBuilding = true;
                    m_selectionWorkingPoints.clear();
                    m_selectionPendingCombineMode = selectionCombineModeForModifiers(modifiers);
                }
                if (!m_selectionWorkingPoints.isEmpty()
                    && m_selectionWorkingPoints.size() >= 3
                    && QLineF(m_selectionWorkingPoints.front(), canvasPoint).length() <= 6.0) {
                    applySelectionPolygon(m_selectionWorkingPoints, m_selectionPendingCombineMode);
                    m_selectionPolylineBuilding = false;
                    m_selectionWorkingPoints.clear();
                } else {
                    m_selectionWorkingPoints.push_back(canvasPoint);
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
            } else {
                m_selectionDragActive = true;
                m_selectionPendingCombineMode = selectionCombineModeForModifiers(modifiers);
                if (m_selectionToolMode == QStringLiteral("rect")) {
                    const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);
                    m_selectionStartCanvasPoint = viewPoint;
                    m_selectionPreviewCanvasPoint = viewPoint;
                } else {
                    m_selectionStartCanvasPoint = canvasPoint;
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
                m_selectionWorkingPoints.clear();
                m_selectionWorkingPoints.push_back(canvasPoint);
            }
            updateSelectionAntsAnimationState();
            update();
            break;
        case QEvent::TabletMove:
            if (m_selectionTranslationActive) {
                updateSelectionTranslation(canvasPoint);
                event->accept();
                return;
            }

            if (m_selectionToolMode == QStringLiteral("polyline")) {
                if (m_selectionPolylineBuilding) {
                    m_selectionPreviewCanvasPoint = canvasPoint;
                    update();
                }
                event->accept();
                return;
            }

            if (m_selectionDragActive) {
                if (m_selectionToolMode == QStringLiteral("rect")) {
                    m_selectionPreviewCanvasPoint = canvasToViewAlignedPoint(canvasPoint);
                } else {
                    m_selectionPreviewCanvasPoint = canvasPoint;
                }
                if (m_selectionToolMode == QStringLiteral("lasso")) {
                    if (!m_selectionWorkingPoints.isEmpty()
                        && m_selectionWorkingPoints.size() >= 3
                        && QLineF(m_selectionWorkingPoints.front(), canvasPoint).length() <= 8.0) {
                        canvasPoint = m_selectionWorkingPoints.front();
                        m_selectionPreviewCanvasPoint = canvasPoint;
                    }
                    if (m_selectionWorkingPoints.isEmpty()
                        || QLineF(m_selectionWorkingPoints.back(), canvasPoint).length() >= 1.2) {
                        m_selectionWorkingPoints.push_back(canvasPoint);
                    }
                }
                update();
            }
            break;
        case QEvent::TabletRelease:
            if (m_selectionTranslationActive) {
                endSelectionTranslation(true);
                event->accept();
                return;
            }

            if (m_selectionDragActive) {
                if (m_selectionToolMode == QStringLiteral("rect")) {
                    const QPointF a = m_selectionStartCanvasPoint;
                    const QPointF b = m_selectionPreviewCanvasPoint;
                    const QVector<QPointF> viewPoly = {
                        QPointF(qMin(a.x(), b.x()), qMin(a.y(), b.y())),
                        QPointF(qMax(a.x(), b.x()), qMin(a.y(), b.y())),
                        QPointF(qMax(a.x(), b.x()), qMax(a.y(), b.y())),
                        QPointF(qMin(a.x(), b.x()), qMax(a.y(), b.y()))
                    };
                    QVector<QPointF> poly;
                    poly.reserve(viewPoly.size());
                    for (const QPointF &vp : viewPoly) {
                        poly.push_back(viewAlignedToCanvasPoint(vp));
                    }
                    applySelectionPolygon(poly, m_selectionPendingCombineMode);
                } else if (m_selectionToolMode == QStringLiteral("lasso")) {
                    if (m_selectionWorkingPoints.size() >= 3
                        && QLineF(m_selectionWorkingPoints.front(), m_selectionWorkingPoints.back()).length() <= 8.0) {
                        m_selectionWorkingPoints.back() = m_selectionWorkingPoints.front();
                    }
                    applySelectionPolygon(m_selectionWorkingPoints, m_selectionPendingCombineMode);
                }
                m_selectionDragActive = false;
                m_selectionWorkingPoints.clear();
                update();
            }
            break;
        default:
            break;
        }

        event->accept();
        return;
    }

    const qreal pressure = qBound(0.05, static_cast<double>(event->pressure()), 1.0);
    const QPointF point = widgetToCanvasPoint(event->position());
    const bool insideCanvas = canvasRect().contains(event->position().toPoint());
    const Qt::KeyboardModifiers modifiers = event->modifiers();

    if (updateColorPickerPreviewFromWidgetPoint(event->position(), modifiers, true, true)
        && event->type() == QEvent::TabletMove) {
        event->accept();
        return;
    }

    if (event->type() == QEvent::TabletPress && insideCanvas
        && tryHandleModifierColorSample(point, modifiers)) {
        updateColorPickerPreviewFromWidgetPoint(event->position(), modifiers, true, true);
        event->accept();
        return;
    }

    if (m_symmetryHandleDragMode != SymmetryHandleDragMode::None) {
        updateSymmetryHandleCursor(event->position());
        if (event->type() == QEvent::TabletMove) {
            updateSymmetryHandleDrag(point);
        } else if (event->type() == QEvent::TabletRelease) {
            endSymmetryHandleDrag();
        }
        event->accept();
        return;
    }

    if ((event->type() == QEvent::TabletMove || event->type() == QEvent::TabletPress)
        && updateSymmetryHandleCursor(event->position())) {
        event->accept();
        return;
    }

    if (m_selectionTranslationActive) {
        if (event->type() == QEvent::TabletMove) {
            updateSelectionTranslation(point);
        } else if (event->type() == QEvent::TabletRelease) {
            endSelectionTranslation(true);
        }
        event->accept();
        return;
    }

    if (m_layerTranslationActive) {
        if (event->type() == QEvent::TabletMove) {
            updateLayerTranslation(point);
        } else if (event->type() == QEvent::TabletRelease) {
            endLayerTranslation(true);
        }
        event->accept();
        return;
    }

    setBrushCursorFromWidgetPoint(event->position(), pressure);

    switch (event->type()) {
    case QEvent::TabletPress:
        if (insideCanvas) {
            if (m_symmetryEnabled) {
                const SymmetryHandleDragMode handleMode = symmetryHandleAtCanvasPoint(point);
                if (handleMode != SymmetryHandleDragMode::None) {
                    beginSymmetryHandleDrag(handleMode, point);
                    event->accept();
                    return;
                }
            }
            if (modifiers.testFlag(Qt::ControlModifier)
                && !modifiers.testFlag(Qt::ShiftModifier)
                && !modifiers.testFlag(Qt::AltModifier)) {
                if (hasSelectionRegion()) {
                    if (m_selectionClipRegion.contains(point.toPoint()) && canMoveSelectionPixels()) {
                        beginSelectionTranslation(point, true);
                        event->accept();
                        return;
                    }
                } else if (canMoveActiveLayerPixels()) {
                    beginLayerTranslation(point);
                    event->accept();
                    return;
                }
            }
            m_straightStrokeActive = modifiers.testFlag(Qt::ShiftModifier);
            m_straightStrokeDragged = false;
            m_straightStrokeStartPoint = point;
            m_straightStrokeStartWidgetPoint = event->position();
            m_straightStrokeEndPoint = point;
            m_straightStrokeEndPressure = pressure;
            if (!m_straightStrokeActive) {
                beginStroke(point, pressure);
            }
        }
        break;
    case QEvent::TabletMove:
        if (m_straightStrokeActive) {
                m_straightStrokeEndPoint = point;
                m_straightStrokeEndPressure = qMax(m_straightStrokeEndPressure, pressure);
                if (QLineF(m_straightStrokeStartWidgetPoint, event->position()).length() >= 3.0) {
                    m_straightStrokeDragged = true;
                }
                update();
        } else if (m_isDrawing) {
            continueStroke(point, pressure);
        }
        break;
    case QEvent::TabletRelease:
        if (m_straightStrokeActive) {
            m_straightStrokeEndPoint = point;
            beginStroke(m_straightStrokeStartPoint, m_straightStrokeEndPressure);
            continueStroke(m_straightStrokeEndPoint, m_straightStrokeEndPressure);
        }
        endStroke();
        m_straightStrokeActive = false;
        forceHideBrushCursor();
        break;
    default:
        break;
    }

    event->accept();
}

void DrawingCanvas::beginStroke(const QPointF &point, qreal pressure)
{
    ensureLayers();
    if (m_selectionToolEnabled) {
        return;
    }
    if (!m_quickAdjustEnabled) {
        return;
    }
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return;
    }

    const RasterLayer &activeLayer = m_layers[m_activeLayerIndex];
    if (isRasterLayerEffectivelyLocked(m_activeLayerIndex) || !isLayerEffectivelyVisible(m_activeLayerIndex)
        || (!m_maskPaintingEnabled && isGroupLayerType(activeLayer.type))
        || (!m_maskPaintingEnabled && isFillLayerType(activeLayer.type))
        ) {
        return;
    }
    // Keep one temporary mask/base for the entire stroke session.
    // Some input paths may restart segments while the pen/mouse is still down.
    if (!m_isDrawing) {
        // A fresh press is a new ownership generation. Late work from a
        // cancelled/replaced stroke is ignored by its generation tag.
        invalidateAsync2dDabs();
        if (m_maskPaintingEnabled && onMaskPaintAboutToChange) {
            onMaskPaintAboutToChange();
        }
        // Mask editing owns a compact, mask-only history in MainWindow.  A
        // regular canvas snapshot would retain the entire layer stack as well
        // and is neither used nor needed while mask mode intercepts Undo.
        if (!m_maskPaintingEnabled) {
            pushUndoHistoryState();
        }
        m_strokeDirtyRect = QRect();
        m_strokeDirtyTiles.clear();
        m_defer2dPreviewComposite = false;
        m_deferred2dPreviewRegion = QRegion();
        m_2dPreviewFrameTimer.stop();
        m_2dStrokePerfTimer.start();
        m_2dPerfDabs = m_2dPerfSprayParticles = m_2dPerfEventBatches = 0;
        m_2dPerfMergedPatches = m_2dPerfTiledPatches = m_2dPerfFallbackParticles = 0;
        m_2dPerfCoverageNs = m_2dPerfPreviewNs = 0;
        m_2dPerfCompositeRegions = m_2dPerfCompositePixels = 0;
        m_pendingCompositeDamageRegion = QRegion();
        m_pendingProjectedCompositeRegion = QRegion();
        m_strokeRandom.seed = QRandomGenerator::global()->generate64();
        m_strokeRandom.nextDab = 0;
        m_strokeRandom.baseAngleDegrees = m_angleDegrees;
        m_strokeRandom.randomAngleDegrees = m_randomAngleDegrees;
        m_strokeRandom.sprayEnabled = m_sprayEnabled;
        m_strokeRandom.sprayRangePercent = m_sprayRangePercent;
        m_strokeRandom.sprayDensity = m_sprayDensity;
        m_strokeRandom.sprayCenterDensityPercent = m_sprayCenterDensityPercent;
        m_strokeRandom.sprayParticleSizePixels = m_sprayParticleSizePixels;
        m_strokeRandom.sprayParticleRandomSizePercent = m_sprayParticleRandomSizePercent;
        m_strokeRandom.sprayParticleRotationDegrees = m_sprayParticleRotationDegrees;
        m_strokeRandom.sprayParticleRandomRotationDegrees = m_sprayParticleRandomRotationDegrees;
        m_strokeRandom.projectedScale = m_projectedStrokeScale;
        ++m_paintCommandGeneration;
        if (m_paintCommandGeneration == 0) ++m_paintCommandGeneration;
        PaintCore::BrushSnapshot paintSnapshot;
        paintSnapshot.strokeId = m_paintCommandGeneration;
        paintSnapshot.generation = m_paintCommandGeneration;
        paintSnapshot.radius = m_baseBrushSize * 0.5;
        paintSnapshot.hardness = m_hardnessPercent / 100.0;
        paintSnapshot.flow = 1.0;
        const qreal baseStrokeOpacity = (m_tool == Tool::Brush || m_maskPaintingEnabled)
            ? qBound(0.0, m_brushInkColor.alphaF(), 1.0) : 1.0;
        paintSnapshot.opacity = qBound(0.0,
            baseStrokeOpacity * (m_opacityPercent / 100.0), 1.0);
        if (m_useTextureTip && !m_maskPaintingEnabled && !m_tipTextureImage.isNull()) {
            paintSnapshot.textureUsesAlpha = m_tipTextureImage.hasAlphaChannel();
            paintSnapshot.textureGamma = 1.0 + (1.0 - qBound(0.01, m_hardnessPercent / 100.0, 1.0)) * 2.5;
            paintSnapshot.textureTip = m_tipTextureImage.convertToFormat(QImage::Format_ARGB32).copy();
        }
        if (hasSelectionRegion()) {
            paintSnapshot.selectionClip = m_selectionClipRegion;
            paintSnapshot.hasSelectionClip = true;
        }
        m_paintCommandStream.begin(std::move(paintSnapshot));
        m_tilingPreviewUpdateTimer.restart();
        m_pendingCompositeDirtyRect = QRect();
        m_pendingCompositeDamageRegion = QRegion();
        // Keep the last complete stack image as the base for this stroke.
        // Subsequent paint events replace only touched tiles in that image.
        m_incrementalCompositeCacheActive = !m_maskPaintingEnabled
                                           && !m_composedCache.isNull()
                                           && m_composedCacheRevision == m_contentRevision;
        // Cache the unchanged layer stack once. During a stroke only the
        // active preview layer changes, so rebuilding every other layer for
        // every tablet packet is unnecessary.
        m_strokeCompositeBackground = QImage();
        m_strokeCompositeForeground = QImage();
        if (!m_maskPaintingEnabled && !canDrawFlatStrokeStackDirectly()
            && m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()
            && !isGroupLayerType(m_layers.at(m_activeLayerIndex).type)) {
            bool flat = true;
            for (int i = 0; i < m_layers.size(); ++i) {
                const RasterLayer &layer = m_layers.at(i);
                if (layer.parentIndex >= 0 || isGroupLayerType(layer.type)) { flat = false; break; }
                // The isolated foreground cache can be safely placed on top
                // only for ordinary opaque layers. Blend modes and partial
                // opacity must see the active layer underneath them, so they
                // retain the full compositor path for correct pixels.
                if (i > m_activeLayerIndex && layer.visible
                    && (layer.blendMode != QStringLiteral("normal")
                        || !qFuzzyCompare(layer.opacityPercent, 100.0))) {
                    flat = false;
                    break;
                }
            }
            if (flat) {
                QVector<bool> visible;
                for (const RasterLayer &layer : std::as_const(m_layers)) visible.push_back(layer.visible);
                for (int i = m_activeLayerIndex; i < m_layers.size(); ++i) m_layers[i].visible = false;
                m_composedCache = QImage(); m_strokeCompositeBackground = composeLayers();
                for (int i = 0; i <= m_activeLayerIndex; ++i) m_layers[i].visible = false;
                for (int i = m_activeLayerIndex + 1; i < m_layers.size(); ++i) m_layers[i].visible = visible.at(i);
                m_composedCache = QImage(); m_strokeCompositeForeground = composeLayers();
                for (int i = 0; i < m_layers.size(); ++i) m_layers[i].visible = visible.at(i);
                m_composedCache = QImage();
            }
        }
        m_nonAccumulatingStrokeActive = false;
        m_strokeBaseImage = QImage();
        m_strokeOverlayImage = QImage();
        m_strokeTransparencyReferenceImage = QImage();
        m_strokePreviewLayerImage = QImage();
        m_maskStrokePreviewImage = QImage();
        m_projectedStrokeObserverActive = false;
        m_experimentalGpuStrokeActive = false;
        if (!m_maskPaintingEnabled && activeLayer.transparentPixelsLocked) {
            // This reference participates in the UI-thread colour composite,
            // but must still be a frozen stroke value rather than a live layer
            // alias while tile workers are preparing coverage.
            m_strokeTransparencyReferenceImage = activeLayer.image.copy();
        }
        if (m_tool == Tool::Brush || m_maskPaintingEnabled || m_projectedStampProvider) {
            if (m_maskPaintingEnabled) m_layers[m_activeLayerIndex].meshMaskFaceIndices.clear();
            if (QImage *layerImage = activeLayerImage()) {
                m_nonAccumulatingStrokeActive = true;
                // The stroke compositor below operates on QRgb scanlines.
                // A layer mask is Grayscale8 (one byte per pixel), so using it
                // directly corrupts neighbouring pixels and produces striped
                // stamps. Composite in RGBA, then convert back on commit.
                m_strokeBaseImage = m_maskPaintingEnabled
                                        ? layerImage->convertToFormat(QImage::Format_ARGB32_Premultiplied)
                                        : *layerImage;
                m_strokePreviewLayerImage = m_strokeBaseImage;
                if (m_maskPaintingEnabled) {
                    // The painter still uses RGBA coverage math for identical
                    // brush results, but presentation stays in its native
                    // one-byte form for the entire stroke.
                    m_maskStrokePreviewImage = *layerImage;
                }
                if (!m_projectedStampProvider || !m_experimentalGpuStrokeBegin || !m_experimentalGpuStrokeSubmit || !m_experimentalGpuStrokeFinish) {
                    // Plain 2D paint needs scalar coverage and lock state only.
                    // Projected paint and layer-mask editing still use the
                    // established QRgb compositor below.
                    const QImage::Format maskFormat = (!m_projectedStampProvider && !m_maskPaintingEnabled)
                        ? QImage::Format_Grayscale8 : QImage::Format_ARGB32_Premultiplied;
                    m_strokeOverlayImage = QImage(layerImage->size(), maskFormat);
                    m_strokeOverlayImage.fill(0);
                }
                m_projectedStrokeObserverActive = bool(m_projectedStampProvider)
                                                 && bool(m_projectedStrokeObserver);
                if (m_projectedStrokeObserverActive) {
                    m_projectedStrokeObserver({ProjectedStrokeEvent::Phase::Begin, QPoint(),
                                               m_strokeBaseImage, QColor(), false});
                }
                m_experimentalGpuStrokeActive = bool(m_projectedStampProvider)
                                                 && bool(m_experimentalGpuStrokeBegin)
                                                 && bool(m_experimentalGpuStrokeSubmit)
                                                 && bool(m_experimentalGpuStrokeFinish);
                if (m_experimentalGpuStrokeActive)
                    m_experimentalGpuStrokeActive = m_experimentalGpuStrokeBegin(m_strokeBaseImage);
            }
        }
        // Keep the chosen path observable. A stroke-level line is deliberately
        // used instead of per-dab logging so performance traces stay readable.
        QStringList paintPathBlocks;
        if (m_strokeOverlayImage.isNull()) paintPathBlocks << QStringLiteral("no-overlay");
        m_paintCoreStrokeActive = m_nonAccumulatingStrokeActive
            && !m_strokeOverlayImage.isNull() && paintPathBlocks.isEmpty();
        if (!m_nonAccumulatingStrokeActive) paintPathBlocks << QStringLiteral("non-accumulating-disabled");
        m_paintPathReason = paintPathBlocks.join(QLatin1Char(','));
        m_paintCoreSubmittedCommandCount = 0;
        m_paintCoreSubmitCoalesceQueued = false;
        if (m_paintCoreStrokeActive) {
            m_paintTileCoordinator.begin(m_paintCommandGeneration);
            BrushPerformance::report(QStringLiteral("[PaintPath] core-tile generation=%1 stroke=%2")
                .arg(m_paintCommandGeneration).arg(m_paintCommandStream.snapshot().strokeId));
        } else {
            BrushPerformance::report(QStringLiteral("[PaintPath] legacy-fallback reason=%1")
                .arg(m_paintPathReason.isEmpty() ? QStringLiteral("unknown") : m_paintPathReason));
        }
    }

    m_isDrawing = true;
    m_pendingProjectedSegment = false;
    m_projectedInterpolationEventCount = 0;
    m_projectedInterpolationDabCount = 0;
    m_projectedInterpolationMultiDabEvents = 0;
    m_projectedInterpolationMaxDabs = 0;
    m_projectedInterpolationReported = false;
    m_lastPoint = point;
    m_lastPressure = pressure;
    m_brushInputSamples.clear();
    m_brushInputSamples.push_back({point, pressure});
    m_inputAverageEventCount = 0;
    m_inputAverageMs = 0.0;
    m_inputAverageReported = false;
    drawDab(point, pressure);
    m_distanceToNextStamp = brushStep(pressure) * (m_projectedStampProvider ? m_projectedSpacingScale : 1.0);
}

void DrawingCanvas::continueStroke(const QPointF &point, qreal pressure)
{
    if (!m_isDrawing || !isLayerEffectivelyVisible(m_activeLayerIndex)) {
        if (m_isDrawing) endStroke();
        return;
    }
    // Blender averages a small circular window of tablet samples before it
    // advances spacing. Two samples filter packet-level jitter while keeping
    // the brush responsive; this deliberately has none of Smooth Stroke's
    // hold radius or visible cursor lag.
    QElapsedTimer inputAverageTimer;
    inputAverageTimer.start();
    constexpr int kBrushInputSamples = 2;
    m_brushInputSamples.push_back({point, pressure});
    if (m_brushInputSamples.size() > kBrushInputSamples) m_brushInputSamples.removeFirst();
    QPointF averagedPoint;
    qreal averagedPressure = 0.0;
    for (const InterpolatedDab &sample : std::as_const(m_brushInputSamples)) {
        averagedPoint += sample.point;
        averagedPressure += sample.pressure;
    }
    averagedPoint /= m_brushInputSamples.size();
    averagedPressure /= m_brushInputSamples.size();
    ++m_inputAverageEventCount;
    m_inputAverageMs += inputAverageTimer.nsecsElapsed() / 1e6;
    drawSegment(m_lastPoint, m_lastPressure, averagedPoint, averagedPressure);
    if (m_pendingProjectedSegment) return;
    m_lastPoint = averagedPoint;
    m_lastPressure = averagedPressure;
}

void DrawingCanvas::endStroke()
{
    if (!m_isDrawing) {
        return;
    }
    if (m_projectedStampProvider && !m_projectedInterpolationReported) {
        BrushPerformance::report(QStringLiteral(
            "[BrushPerf][Interpolation] events=%1 dabs=%2 multiDabEvents=%3 maxDabs=%4")
            .arg(m_projectedInterpolationEventCount)
            .arg(m_projectedInterpolationDabCount)
            .arg(m_projectedInterpolationMultiDabEvents)
            .arg(m_projectedInterpolationMaxDabs));
        m_projectedInterpolationReported = true;
    }
    if (m_inputAverageEventCount && !m_inputAverageReported) {
        BrushPerformance::report(QStringLiteral(
            "[BrushPerf][InputAverage] samples=2 events=%1 totalMs=%2 avgUs=%3")
            .arg(m_inputAverageEventCount)
            .arg(m_inputAverageMs, 0, 'f', 4)
            .arg(m_inputAverageMs * 1000.0 / m_inputAverageEventCount, 0, 'f', 3));
        m_inputAverageReported = true;
    }
    if (!m_projectedStampProvider && m_2dStrokePerfTimer.isValid()) {
        BrushPerformance::report(QStringLiteral(
            "[BrushPerf][2DStroke] elapsedMs=%1 dabs=%2 eventBatches=%3 sprayParticles=%4 mergedPatches=%5 tiledPatches=%6 fallbackParticles=%7 coverageMs=%8 deferredPreviewMs=%9 compositeRegions=%10 compositePixels=%11")
            .arg(m_2dStrokePerfTimer.nsecsElapsed() / 1e6, 0, 'f', 3)
            .arg(m_2dPerfDabs).arg(m_2dPerfEventBatches).arg(m_2dPerfSprayParticles)
            .arg(m_2dPerfMergedPatches).arg(m_2dPerfTiledPatches).arg(m_2dPerfFallbackParticles)
            .arg(m_2dPerfCoverageNs / 1e6, 0, 'f', 3)
            .arg(m_2dPerfPreviewNs / 1e6, 0, 'f', 3)
            .arg(m_2dPerfCompositeRegions).arg(m_2dPerfCompositePixels));
    }
    if (m_pendingProjectedSegment) {
        m_projectedSliceBudget = -1;
        drawSegment(m_lastPoint, m_lastPressure, m_projectedSegmentTarget, m_projectedSegmentPressure);
    }
    if (m_experimentalGpuStrokeActive && m_experimentalGpuStrokeFinish) {
        if (m_gpuStrokeFinishPending) return;
        if (!m_experimentalGpuStrokeSubmit || !m_experimentalGpuStrokeSubmit()) {
            m_experimentalGpuStrokeActive = false;
            endStroke();
            return;
        }
        m_gpuStrokeFinishPending = true;
        const auto completeGpuStroke = [this](const ExperimentalGpuStrokeFinishResult &gpuFinish,
                                              const QVector<QRect> &gpuDamage) {
            m_gpuStrokeFinishPending = false;
            if (gpuFinish.state == ExperimentalGpuStrokeFinishState::Complete
                && !gpuFinish.image.isNull() && gpuFinish.image.size() == m_strokePreviewLayerImage.size()) {
                const QImage &gpuResult = gpuFinish.image;
                m_strokePreviewLayerImage = gpuResult.convertToFormat(m_strokePreviewLayerImage.format());
                if (m_maskPaintingEnabled) m_maskStrokePreviewImage = QImage();
                m_composedCache = QImage();
                m_incrementalCompositeCacheActive = false;
                for (const QRect &region : gpuDamage) {
                    const QRect dirty = region.intersected(QRect(QPoint(), m_documentSize));
                    if (dirty.isEmpty()) continue;
                    m_strokeDirtyRect = m_strokeDirtyRect.isNull() ? dirty : m_strokeDirtyRect.united(dirty);
                    for (int row = dirty.top() / 128; row <= dirty.bottom() / 128; ++row)
                        for (int column = dirty.left() / 128; column <= dirty.right() / 128; ++column)
                            m_strokeDirtyTiles.insert(QPoint(column, row));
                }
            }
            m_experimentalGpuStrokeActive = false;
            endStroke();
        };
        // Mask readback is deliberately completed synchronously on release so
        // the very next press must see its result.  Commit it immediately
        // rather than waiting for a zero-delay event turn.
        const QVector<QRect> immediateDamage = m_experimentalGpuStrokeDamage
            ? m_experimentalGpuStrokeDamage() : QVector<QRect>();
        const ExperimentalGpuStrokeFinishResult immediateFinish = m_experimentalGpuStrokeFinish();
        if (immediateFinish.state != ExperimentalGpuStrokeFinishState::Pending) {
            completeGpuStroke(immediateFinish, immediateDamage);
            return;
        }
        // Do not block the pointer-release handler on glReadPixels.  The 3D
        // viewport retains its GPU preview texture while this queued callback
        // resolves the CPU image and resumes the ordinary commit path below.
        QTimer::singleShot(0, this, [this, completeGpuStroke] {
            if (!m_gpuStrokeFinishPending || !m_isDrawing) return;
            const QVector<QRect> gpuDamage = m_experimentalGpuStrokeDamage
                ? m_experimentalGpuStrokeDamage() : QVector<QRect>();
            const ExperimentalGpuStrokeFinishResult gpuFinish = m_experimentalGpuStrokeFinish();
            if (gpuFinish.state == ExperimentalGpuStrokeFinishState::Pending) {
                m_gpuStrokeFinishPending = false;
                QTimer::singleShot(1, this, [this] { endStroke(); });
                return;
            }
            completeGpuStroke(gpuFinish, gpuDamage);
        });
        return;
    }
    if (m_nonAccumulatingStrokeActive && !m_strokePreviewLayerImage.isNull()) {
        if (m_paintCoreStrokeActive) {
            finishPaintCoreStroke();
            m_2dPreviewFrameTimer.stop();
            flushDeferred2dStrokePreview();
        } else if (!m_projectedStampProvider) {
            finishAsync2dStroke();
            m_2dPreviewFrameTimer.stop();
            flushDeferred2dStrokePreview();
        }
        if (QImage *layerImage = activeLayerImage()) {
            *layerImage = m_maskPaintingEnabled && !m_maskStrokePreviewImage.isNull()
                              ? m_maskStrokePreviewImage
                              : (m_maskPaintingEnabled
                                     ? m_strokePreviewLayerImage.convertToFormat(QImage::Format_Grayscale8)
                                     : m_strokePreviewLayerImage);
        }
    }

    if (m_projectedStrokeObserverActive && m_projectedStrokeObserver) {
        m_projectedStrokeObserver({ProjectedStrokeEvent::Phase::End, QPoint(),
                                   m_strokePreviewLayerImage, QColor(), false});
    }

    // Flush the last coalesced tile before leaving stroke mode. This keeps the
    // display cache ready for the next pen-down instead of forcing a complete
    // stack rebuild between two quick strokes.
    if (m_incrementalCompositeCacheActive && !m_pendingCompositeDirtyRect.isEmpty()) {
        composeLayers();
    }

    m_isDrawing = false;
    m_brushInputSamples.clear();
    m_distanceToNextStamp = 0.0;
    m_nonAccumulatingStrokeActive = false;
    m_paintCoreStrokeActive = false;
    m_paintCoreSubmitCoalesceQueued = false;
    m_strokeBaseImage = QImage();
    m_strokeOverlayImage = QImage();
    m_strokeTransparencyReferenceImage = QImage();
    m_strokePreviewLayerImage = QImage();
    m_maskStrokePreviewImage = QImage();
    m_projectedStrokeObserverActive = false;
    m_experimentalGpuStrokeActive = false;
    m_strokeCompositeBackground = QImage();
    m_strokeCompositeForeground = QImage();
    m_pendingCompositeDirtyRect = QRect();
    m_pendingCompositeDamageRegion = QRegion();
    m_incrementalCompositeCacheActive = false;
    bumpContentRevision();
    if (!m_composedCache.isNull()) {
        m_composedCacheRevision = m_contentRevision;
    }
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    if (m_tilingPreviewEnabled) {
        m_tilingPreviewUpdateTimer.invalidate();
        update(canvasRect().intersected(rect()));
    }
}

void DrawingCanvas::beginQuickAdjust(QuickAdjustMode mode)
{
    if (!m_quickAdjustEnabled || m_selectionToolEnabled || mode == QuickAdjustMode::None) {
        return;
    }

    if (m_isDrawing) {
        endStroke();
    }

    const QRect art = canvasRect();
    QPoint widgetAnchor = mapFromGlobal(QCursor::pos());
    widgetAnchor.setX(qBound(art.left(), widgetAnchor.x(), art.right()));
    widgetAnchor.setY(qBound(art.top(), widgetAnchor.y(), art.bottom()));

    m_quickAdjustMode = mode;
    m_quickAdjustAnchorWidgetPoint = QPointF(widgetAnchor);
    m_quickAdjustAnchorCanvasPoint = widgetToCanvasPoint(QPointF(widgetAnchor));
    m_quickAdjustPreviewValue = (mode == QuickAdjustMode::BrushSize)
                                    ? qMax(1, m_baseBrushSize)
                                    : qBound(0, m_opacityPercent, 100);
    // Shift+F adjusts relative to the opacity that was active when the
    // gesture began, so moving left/right from the anchor decreases/increases it.
    m_quickAdjustStartValue = m_quickAdjustPreviewValue;
    if (mode == QuickAdjustMode::BrushSize) {
        const QRect display = documentDisplayRect();
        const qreal sx = qreal(qMax(1, m_documentSize.width() - 1)) / qMax(1, display.width() - 1);
        const qreal sy = qreal(qMax(1, m_documentSize.height() - 1)) / qMax(1, display.height() - 1);
        const qreal radius = m_quickAdjustPreviewValue * 0.5 / qMax(0.0001, (sx + sy) * 0.5);
        const qreal offset = radius / std::sqrt(2.0);
        m_quickAdjustAnchorWidgetPoint -= QPointF(offset, offset);
        m_quickAdjustAnchorCanvasPoint = widgetToCanvasPoint(m_quickAdjustAnchorWidgetPoint);
    }
    setBrushCursorVisible(false);
    grabMouse();
    update();
}

qreal DrawingCanvas::quickAdjustDistanceToCanvasUnits(const QPointF &widgetPoint) const
{
    const QPointF anchorWidget = m_tilingPreviewEnabled
                                     ? m_quickAdjustAnchorWidgetPoint
                                     : canvasToWidgetPoint(m_quickAdjustAnchorCanvasPoint);
    const qreal distWidget = QLineF(anchorWidget, widgetPoint).length();
    const QRect art = documentDisplayRect();
    const qreal sx = static_cast<qreal>(qMax(1, m_documentSize.width() - 1))
                     / static_cast<qreal>(qMax(1, art.width() - 1));
    const qreal sy = static_cast<qreal>(qMax(1, m_documentSize.height() - 1))
                     / static_cast<qreal>(qMax(1, art.height() - 1));
    const qreal scale = qMax(0.0001, (sx + sy) * 0.5);
    return distWidget * scale;
}

void DrawingCanvas::updateQuickAdjustFromWidgetPoint(const QPointF &widgetPoint)
{
    if (m_quickAdjustMode == QuickAdjustMode::None) {
        return;
    }

    const qreal distCanvas = quickAdjustDistanceToCanvasUnits(widgetPoint);
    int value = 0;
    if (m_quickAdjustMode == QuickAdjustMode::BrushSize) {
        value = qBound(1, static_cast<int>(std::lround(distCanvas * 2.0)), 1000);
    } else {
        const qreal deltaX = widgetPoint.x() - m_quickAdjustAnchorWidgetPoint.x();
        value = qBound(0, m_quickAdjustStartValue + static_cast<int>(std::lround(deltaX / 3.0)), 100);
    }

    if (m_quickAdjustPreviewValue != value) {
        m_quickAdjustPreviewValue = value;
        update();
    }
}

void DrawingCanvas::commitQuickAdjust()
{
    if (m_quickAdjustMode == QuickAdjustMode::None) {
        return;
    }

    if (m_quickAdjustMode == QuickAdjustMode::BrushSize) {
        setBrushSize(qMax(1, m_quickAdjustPreviewValue));
    } else {
        setOpacity(qBound(0, m_quickAdjustPreviewValue, 100));
    }

    m_quickAdjustMode = QuickAdjustMode::None;
    if (QWidget::mouseGrabber() == this) releaseMouse();
    update();
}

void DrawingCanvas::cancelQuickAdjust()
{
    if (m_quickAdjustMode == QuickAdjustMode::None) {
        return;
    }
    m_quickAdjustMode = QuickAdjustMode::None;
    if (QWidget::mouseGrabber() == this) releaseMouse();
    update();
}

void DrawingCanvas::drawInterpolatedDabBatch(const QVector<InterpolatedDab> &dabs)
{
    if (dabs.isEmpty()) {
        return;
    }

    // Do not add collection overhead to the established one-dab path.
    // The event path below is only useful once interpolation actually created
    // two or more stamps.
    if (dabs.size() == 1) {
        if (m_projectedStampProvider) {
            ++m_projectedInterpolationEventCount;
            ++m_projectedInterpolationDabCount;
            m_projectedInterpolationMaxDabs = qMax(m_projectedInterpolationMaxDabs, 1);
        }
        drawDab(dabs.front().point, dabs.front().pressure);
        return;
    }

    // A retained GPU stroke can now preflight every resolved dab and submit its
    // complete event in one provider call. Single dabs remain on drawDab().
    const bool submitAsEvent = m_experimentalGpuStrokeActive
        && bool(m_projectedStampProvider) && bool(m_projectedStampBatchProvider);
    if (m_projectedStampProvider) {
        ++m_projectedInterpolationEventCount;
        m_projectedInterpolationDabCount += dabs.size();
        if (dabs.size() > 1) ++m_projectedInterpolationMultiDabEvents;
        m_projectedInterpolationMaxDabs = qMax(m_projectedInterpolationMaxDabs, dabs.size());
    }
    m_collectProjectedEventInstances = submitAsEvent;
    m_projectedEventInstances.clear();
    // 2D keeps coverage/lock updates in dab order, but its preview conversion
    // is independent of that order once coverage is complete. Coalescing it
    // here prevents one tablet event with several interpolated dabs from
    // repeatedly rewriting the same RGBA preview pixels.
    const bool defer2dPreview = !m_projectedStampProvider && m_nonAccumulatingStrokeActive;
    if (defer2dPreview) {
        ++m_2dPerfEventBatches;
        m_defer2dPreviewComposite = true;
        m_collect2dCoverageCommands = true;
    }
    // One tablet event can expand to many symmetry copies. Defer submission
    // until all of them are recorded so the tile worker sees one larger batch.
    const bool deferSymmetrySubmit = m_paintCoreStrokeActive && m_symmetryEnabled;
    const bool previousDeferPaintCoreSubmit = m_deferPaintCoreSubmit;
    if (deferSymmetrySubmit) m_deferPaintCoreSubmit = true;
    for (const InterpolatedDab &dab : dabs) {
        drawDab(dab.point, dab.pressure);
    }
    m_deferPaintCoreSubmit = previousDeferPaintCoreSubmit;
    if (deferSymmetrySubmit) submitPaintCoreTiles();
    if (defer2dPreview) {
        m_collect2dCoverageCommands = false;
        flushQueued2dCoverageCommands();
        m_defer2dPreviewComposite = false;
        scheduleDeferred2dStrokePreview();
    }
    m_collectProjectedEventInstances = false;
    if (submitAsEvent && !m_projectedEventInstances.isEmpty()) {
        m_projectedStampBatchProvider(m_projectedEventInstances);
    }
    m_projectedEventInstances.clear();
}

void DrawingCanvas::drawSegment(const QPointF &from, qreal fromPressure, const QPointF &to, qreal toPressure)
{
    QPointF unwrappedTo = to;
    if (m_tilingPreviewEnabled) {
        const qreal periodX = qMax(1, m_documentSize.width());
        const qreal periodY = qMax(1, m_documentSize.height());
        qreal dx = unwrappedTo.x() - from.x();
        qreal dy = unwrappedTo.y() - from.y();
        if (dx > periodX * 0.5) {
            unwrappedTo.rx() -= periodX;
        } else if (dx < -periodX * 0.5) {
            unwrappedTo.rx() += periodX;
        }
        if (dy > periodY * 0.5) {
            unwrappedTo.ry() -= periodY;
        } else if (dy < -periodY * 0.5) {
            unwrappedTo.ry() += periodY;
        }
    }

    const QPointF delta = unwrappedTo - from;
    const qreal length = std::hypot(delta.x(), delta.y());
    if (length <= 0.0001) {
        return;
    }

    // Projection painting spaces dabs on the visible surface, rather than in
    // screen pixels.  This is the important distinction in Blender's Texture
    // Paint path: a retreating surface receives the same physical spacing as
    // a foreground surface.  The projector also makes the intermediate dabs
    // follow the perspective projection of the surface chord.
    std::optional<QVector3D> surfaceFrom;
    std::optional<QVector3D> surfaceTo;
    const bool canUseSceneSpacing = m_projectedStampProvider && m_projectedSurfaceHitProvider
        && m_projectedWorldProjector
        && (surfaceFrom = m_projectedSurfaceHitProvider(from)).has_value()
        && (surfaceTo = m_projectedSurfaceHitProvider(unwrappedTo)).has_value();
    const QVector3D surfaceDelta = canUseSceneSpacing ? (*surfaceTo - *surfaceFrom) : QVector3D();
    const qreal sceneLength = canUseSceneSpacing ? surfaceDelta.length() : length;
    const qreal sceneUnitsPerScreenPixel = canUseSceneSpacing
        ? sceneLength / qMax<qreal>(length, 1e-6) : 1.0;
    if (!canUseSceneSpacing) {
        m_projectedSceneSpacingActive = false;
        // Blender's scene-spacing path does not bridge a missing raycast hit
        // with screen-space dabs. Wait for the next valid surface point and
        // restart spacing there.
        if (m_projectedStampProvider && m_projectedSurfaceHitProvider && m_projectedWorldProjector) {
            m_distanceToNextStamp = 0.0;
            return;
        }
    }

    auto wrapPoint = [this](const QPointF &point) {
        if (!m_tilingPreviewEnabled) {
            return point;
        }
        const qreal periodX = qMax(1, m_documentSize.width());
        const qreal periodY = qMax(1, m_documentSize.height());
        qreal x = std::fmod(point.x(), periodX);
        qreal y = std::fmod(point.y(), periodY);
        if (x < 0.0) {
            x += periodX;
        }
        if (y < 0.0) {
            y += periodY;
        }
        return QPointF(x, y);
    };

    qreal progressed = m_pendingProjectedSegment ? m_projectedSegmentProgress : 0.0;
    qreal remainingToNext = m_pendingProjectedSegment ? m_projectedSegmentRemaining : m_distanceToNextStamp;
    m_pendingProjectedSegment = false;
    if (canUseSceneSpacing && !m_projectedSceneSpacingActive) {
        // The previous residual was in screen pixels (or belongs to a surface
        // which was lost). Restarting at the next physical spacing is the same
        // discontinuity behaviour Blender uses when its raycast has no hit.
        remainingToNext = brushStep(fromPressure) * sceneUnitsPerScreenPixel;
        m_projectedSceneSpacingActive = true;
    }
    if (remainingToNext <= 0.0) {
        remainingToNext = brushStep(fromPressure) * (m_projectedStampProvider ? m_projectedSpacingScale : 1.0);
    }

    // External 3D input reaches this method through the six-millisecond slice
    // budget.  It must take the same collection path as direct input; otherwise
    // every interpolated dab is submitted immediately and no event batching can
    // occur in the real painting path.  Bound a micro-batch so a large pointer
    // jump cannot turn one input sample into an unbounded synchronous submit.
    const bool collectEventDabs = (m_projectedStampProvider
        && m_experimentalGpuStrokeActive && bool(m_projectedStampBatchProvider))
        || (!m_projectedStampProvider && m_nonAccumulatingStrokeActive);
    constexpr int kProjectedEventDabBatchLimit = 8;
    QVector<InterpolatedDab> eventDabs;
    eventDabs.reserve(kProjectedEventDabBatchLimit);

    while (progressed + remainingToNext <= sceneLength) {
        progressed += remainingToNext;
        const qreal t = progressed / sceneLength;
        const QPointF stampPos = wrapPoint(canUseSceneSpacing
            ? m_projectedWorldProjector(*surfaceFrom + surfaceDelta * t)
            : from + delta * t);
        const qreal pressure = fromPressure + (toPressure - fromPressure) * t;
        if (collectEventDabs) {
            eventDabs.push_back({stampPos, pressure});
            if (eventDabs.size() == kProjectedEventDabBatchLimit) {
                drawInterpolatedDabBatch(eventDabs);
                eventDabs.clear();
            }
        } else {
            drawDab(stampPos, pressure);
        }
        // Blender's variable-spacing path uses the average of the current and
        // next pressure-sized brush.  Using just this dab's pressure makes a
        // rapid pressure ramp alternate between visibly dense and sparse
        // stamps. Estimate the next sample along this segment, then retain the
        // average centre-to-centre distance.
        const qreal spacingScale = canUseSceneSpacing ? sceneUnitsPerScreenPixel
            : (m_projectedStampProvider ? m_projectedSpacingScale : 1.0);
        const qreal currentStep = brushStep(pressure) * spacingScale;
        const qreal nextProgress = qMin(sceneLength, progressed + currentStep);
        const qreal nextPressure = fromPressure + (toPressure - fromPressure)
            * (nextProgress / qMax<qreal>(sceneLength, 1e-6));
        remainingToNext = 0.5 * (currentStep + brushStep(nextPressure) * spacingScale);
        if (m_projectedStampProvider && m_projectedSliceBudget >= 0
            && m_projectedSliceTimer.elapsed() >= m_projectedSliceBudget
            && progressed + remainingToNext <= sceneLength) {
            m_pendingProjectedSegment = true;
            m_projectedSegmentProgress = progressed;
            m_projectedSegmentRemaining = remainingToNext;
            m_projectedSegmentTarget = to;
            m_projectedSegmentPressure = toPressure;
            if (collectEventDabs && !eventDabs.isEmpty()) {
                drawInterpolatedDabBatch(eventDabs);
            }
            return;
        }
    }

    if (collectEventDabs) {
        drawInterpolatedDabBatch(eventDabs);
    }

    m_distanceToNextStamp = remainingToNext - (sceneLength - progressed);

    if (m_distanceToNextStamp < 0.01) {
        m_distanceToNextStamp = 0.01;
    }

    if (m_projectedStampProvider) return;

    // Repaint only the stroke's dirty area instead of the whole widget.
    const QRect artRect = canvasRect();
    const QPointF w0 = canvasToWidgetPoint(from);
    const QPointF w1 = canvasToWidgetPoint(to);

    const qreal pressureMax = qMax(fromPressure, toPressure);
    const qreal radiusCanvasX = brushPreviewRadiusPx(pressureMax);
    const qreal radiusCanvasY = qMax(0.5, radiusCanvasX * (m_roundnessPercent / 100.0));
    const qreal sx = qMax(1, artRect.width() - 1) / static_cast<qreal>(qMax(1, m_documentSize.width() - 1));
    const qreal sy = qMax(1, artRect.height() - 1) / static_cast<qreal>(qMax(1, m_documentSize.height() - 1));
    // A spray particle can land one spread radius away from the input point.
    // The old dirty range used only the ordinary brush radius, which made the
    // live 2D preview look rectangularly clipped until endStroke repainted the
    // complete document.
    const bool strokeSpray = m_isDrawing ? m_strokeRandom.sprayEnabled : m_sprayEnabled;
    const qreal sprayRange = (m_isDrawing ? m_strokeRandom.sprayRangePercent : m_sprayRangePercent) / 100.0;
    const qreal maxParticlePixels = qMax<qreal>(1.0,
        (m_isDrawing ? m_strokeRandom.sprayParticleSizePixels : m_sprayParticleSizePixels)
        * (1.0 + (m_isDrawing ? m_strokeRandom.sprayParticleRandomSizePercent
                               : m_sprayParticleRandomSizePercent) / 100.0));
    const qreal sprayExtent = strokeSpray
        ? radiusCanvasX * sprayRange + std::sqrt(2.0) * maxParticlePixels + 3.0
        : 0.0;
    const qreal paintExtentX = qMax(radiusCanvasX, sprayExtent);
    const qreal paintExtentY = qMax(radiusCanvasY, sprayExtent);
    const qreal padX = paintExtentX * sx + 4.0;
    const qreal padY = paintExtentY * sy + 4.0;

    QRectF dirty(QPointF(qMin(w0.x(), w1.x()), qMin(w0.y(), w1.y())),
                 QPointF(qMax(w0.x(), w1.x()), qMax(w0.y(), w1.y())));
    dirty = dirty.adjusted(-padX, -padY, padX, padY);
    // Keep GPU upload damage in document pixels, not widget pixels. Using the
    // display-space dirty rectangle here made partial 3D uploads too large at
    // some zoom levels and incorrect at others.
    QRectF textureDirty;
    QRegion textureDamageRegion;
    const auto includeTextureStamp = [&](const QPointF &canvasPoint) {
        const QRectF stampRect(canvasPoint.x() - paintExtentX - 2.0,
                               canvasPoint.y() - paintExtentY - 2.0,
                               paintExtentX * 2.0 + 4.0,
                               paintExtentY * 2.0 + 4.0);
        textureDirty = textureDirty.isNull() ? stampRect : textureDirty.united(stampRect);
        textureDamageRegion += stampRect.toAlignedRect().intersected(QRect(QPoint(), m_documentSize));
    };
    if (m_tilingPreviewEnabled) {
        textureDirty = QRectF(QPointF(0, 0), QSizeF(m_documentSize));
        textureDamageRegion = QRegion(QRect(QPoint(), m_documentSize));
    } else if (m_symmetryEnabled && m_symmetrySegments > 1) {
        const QVector<QPointF> mirroredFromForTexture = symmetryStampPoints(from);
        const QVector<QPointF> mirroredToForTexture = symmetryStampPoints(to);
        for (const QPointF &p : mirroredFromForTexture) includeTextureStamp(p);
        for (const QPointF &p : mirroredToForTexture) includeTextureStamp(p);
    } else {
        includeTextureStamp(from);
        includeTextureStamp(to);
    }
    if (!m_tilingPreviewEnabled) {
        textureDamageRegion = QRegion();
        if (m_symmetryEnabled && m_symmetrySegments > 1) {
            const QVector<QPointF> mirroredFrom = symmetryStampPoints(from);
            const QVector<QPointF> mirroredTo = symmetryStampPoints(to);
            const int count = qMin(mirroredFrom.size(), mirroredTo.size());
            for (int i = 0; i < count; ++i) {
                const QPointF &a = mirroredFrom.at(i);
                const QPointF &b = mirroredTo.at(i);
                const QRectF pathBounds(QPointF(qMin(a.x(), b.x()) - paintExtentX - 2.0,
                                               qMin(a.y(), b.y()) - paintExtentY - 2.0),
                                       QPointF(qMax(a.x(), b.x()) + paintExtentX + 2.0,
                                               qMax(a.y(), b.y()) + paintExtentY + 2.0));
                textureDamageRegion += pathBounds.toAlignedRect().intersected(QRect(QPoint(), m_documentSize));
            }
        } else {
            textureDamageRegion = QRegion(textureDirty.toAlignedRect().intersected(QRect(QPoint(), m_documentSize)));
        }
    }
    const QRect textureDirtyRect = textureDirty.toAlignedRect().intersected(QRect(QPoint(0, 0), m_documentSize));
    if (!textureDirtyRect.isEmpty()) {
        m_strokeDirtyRect = m_strokeDirtyRect.isNull()
                                 ? textureDirtyRect
                                 : m_strokeDirtyRect.united(textureDirtyRect);
        m_pendingCompositeDirtyRect = m_pendingCompositeDirtyRect.isNull()
                                           ? textureDirtyRect
                                           : m_pendingCompositeDirtyRect.united(textureDirtyRect);
        // Distant symmetry copies must not force composition of their empty
        // bounding rectangle. Keep their document-space damage as islands.
        m_pendingCompositeDamageRegion += textureDamageRegion;
    }
    if (m_tilingPreviewEnabled) {
        // A tiled stroke invalidates every repeated copy.  Tablet packets can
        // arrive far faster than the widget can repaint nine copies, so cap
        // those full-preview redraws to the display cadence.
        if (!m_tilingPreviewUpdateTimer.isValid()
            || m_tilingPreviewUpdateTimer.elapsed() >= 16) {
            m_tilingPreviewUpdateTimer.restart();
            update(canvasRect().intersected(rect()));
        }
    } else if (m_symmetryEnabled && m_symmetrySegments > 1) {
        // Symmetry used to repaint the complete canvas for every stroke segment.
        // Repaint just the corresponding dirty segment for each mirrored copy.
        const QVector<QPointF> mirroredFrom = symmetryStampPoints(from);
        const QVector<QPointF> mirroredTo = symmetryStampPoints(to);
        const int count = qMin(mirroredFrom.size(), mirroredTo.size());
        for (int i = 0; i < count; ++i) {
            const QPointF fromWidget = canvasToWidgetPoint(mirroredFrom.at(i));
            const QPointF toWidget = canvasToWidgetPoint(mirroredTo.at(i));
            QRectF mirroredDirty(QPointF(qMin(fromWidget.x(), toWidget.x()), qMin(fromWidget.y(), toWidget.y())),
                                 QPointF(qMax(fromWidget.x(), toWidget.x()), qMax(fromWidget.y(), toWidget.y())));
            mirroredDirty = mirroredDirty.adjusted(-padX, -padY, padX, padY);
            update(mirroredDirty.toAlignedRect().intersected(rect()));
        }
    } else {
        update(dirty.toAlignedRect().intersected(rect()));
    }
}

void DrawingCanvas::drawDab(const QPointF &point, qreal pressure)
{
    if (!m_projectedStampProvider)
        ++m_2dPerfDabs;
    const StrokeRandomState &strokeRandom = m_strokeRandom;
    const quint64 dabIndex = m_strokeRandom.nextDab++;
    const auto random01 = [&strokeRandom, dabIndex](int symmetryIndex, int particleIndex, int channel) {
        return strokeRandom01(strokeRandom.seed, dabIndex, quint64(symmetryIndex),
                              quint64(particleIndex), quint64(channel));
    };
    const qreal sizeFactor = sizePressureFactor(pressure);
    const qreal opacityFactor = opacityPressureFactor(pressure);

    const qreal radiusX = qMax(0.5, (m_baseBrushSize * sizeFactor) * 0.5);
    const qreal radiusY = qMax(0.5, radiusX * (m_roundnessPercent / 100.0));

    QColor color;
    if (m_maskPaintingEnabled) {
        // A mask's paint value follows the artist-facing HSL Lightness
        // control, not perceptual/RGB luma.  Saturated red, green and blue at
        // the same HSL lightness must therefore write the same mask value.
        const int grayscale = (m_tool == Tool::Eraser)
                                  ? 0
                                  : m_brushInkColor.lightness();
        color = QColor(grayscale, grayscale, grayscale);
    } else {
        color = (m_tool == Tool::Brush) ? m_brushInkColor : QColor(Qt::white);
    }
    const qreal baseAlpha = (m_tool == Tool::Brush || m_maskPaintingEnabled)
                                ? qBound(0.0, color.alphaF(), 1.0) : 1.0;
    qreal finalAlpha = qBound(0.0, baseAlpha * (m_opacityPercent / 100.0) * opacityFactor, 1.0);
    if (!m_nonAccumulatingStrokeActive && !strokeRandom.sprayEnabled && finalAlpha > 0.0) {
        const qreal step = brushStep(pressure);
        const qreal diameter = qMax(1.0, radiusX * 2.0);
        const qreal coverage = qBound(0.05, step / diameter, 1.0);
        finalAlpha = 1.0 - std::pow(1.0 - finalAlpha, coverage);
    }
    if (finalAlpha <= 0.0001) {
        return;
    }
    // Keep the original direct-opacity behaviour: every dab uses the selected
    // opacity.  This deliberately allows visible overlap at wide spacing, but
    // avoids making soft/airbrush strokes require repeated passes for colour.
    const qreal dabAlpha = finalAlpha;
    // Pressure produces a near-continuous alpha stream.  Caching an individual
    // raster tip for every one of those values both thrashes the stamp cache and
    // repeatedly rebuilds gradients/texture tips. 64 levels keep normal-flow
    // transitions smooth while making tip reuse common.
    constexpr int kCachedAlphaLevels = 64;
    const int cachedDabAlpha = qBound(0, static_cast<int>(std::lround(
                                           qBound(0.0, dabAlpha, 1.0)
                                           * static_cast<qreal>(kCachedAlphaLevels - 1))),
                                      kCachedAlphaLevels - 1);
    const qreal cachedDabAlphaF = static_cast<qreal>(cachedDabAlpha)
                                  / static_cast<qreal>(kCachedAlphaLevels - 1);
    color.setAlphaF(cachedDabAlphaF);

    const int stampRx = qMax(1, static_cast<int>(std::ceil(radiusX)));
    const int stampRy = qMax(1, static_cast<int>(std::ceil(radiusY)));
    // All brush modes use the same tip and compositor.  A soft brush is an
    // airbrush through its hardness/flow settings, not through a second
    // rasterisation path with different overlap rules.
    const int stampHardness = m_hardnessPercent;
    // Masks are scalar images. Keep their strokes continuous and independent
    // of colour-tip patterns; patterned alpha tips were the source of visible
    // stripe artifacts in grayscale masks.
    const bool useTextureStamp = m_useTextureTip && !m_maskPaintingEnabled;
    const quint64 stampKey = makeBrushStampKey(stampRx,
                                                 stampRy,
                                                 stampHardness,
                                                 color.rgba(),
                                                 useTextureStamp,
                                                m_tipTextureToken);
    auto it = m_brushStampCache.constFind(stampKey);
    if (it == m_brushStampCache.constEnd()) {
        if (m_brushStampCache.size() > 512) {
            m_brushStampCache.clear();
            m_brushStampMaxAlphaCache.clear();
        }
        const QImage stamp = makeBrushStampImage(stampRx, stampRy, stampHardness, color);
        it = m_brushStampCache.insert(stampKey, stamp);
    }
    const QImage &stamp = it.value();
    QVector<QPointF> symmetryCenters = symmetryStampPoints(point);
    QVector<qreal> symmetryRotations;
    symmetryRotations.reserve(symmetryCenters.size());
    for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
        const qreal randomAngle = (random01(symmetryIndex, 0, 0) * 2.0 - 1.0)
                                  * strokeRandom.randomAngleDegrees;
        symmetryRotations.push_back(strokeRandom.baseAngleDegrees + randomAngle);
    }
    if (m_tilingPreviewEnabled) {
        const QVector<QPointF> baseCenters = symmetryCenters;
        const QVector<qreal> baseRotations = symmetryRotations;
        const qreal width = qMax(1, m_documentSize.width());
        const qreal height = qMax(1, m_documentSize.height());
        for (int baseIndex = 0; baseIndex < baseCenters.size(); ++baseIndex) {
            const QPointF &center = baseCenters.at(baseIndex);
            QVector<qreal> xOffsets = {0.0};
            QVector<qreal> yOffsets = {0.0};
            if (center.x() < radiusX + 1.0) {
                xOffsets.push_back(width);
            }
            if (center.x() > width - radiusX - 1.0) {
                xOffsets.push_back(-width);
            }
            if (center.y() < radiusY + 1.0) {
                yOffsets.push_back(height);
            }
            if (center.y() > height - radiusY - 1.0) {
                yOffsets.push_back(-height);
            }
            for (qreal xOffset : std::as_const(xOffsets)) {
                for (qreal yOffset : std::as_const(yOffsets)) {
                    if (qFuzzyIsNull(xOffset) && qFuzzyIsNull(yOffset)) {
                        continue;
                    }
                    symmetryCenters.push_back(center + QPointF(xOffset, yOffset));
                    symmetryRotations.push_back(baseRotations.at(baseIndex));
                }
            }
        }
    }

    // Projection itself is context-owned and therefore resolves here on the UI
    // thread. Its returned texture-space coverage is immediately frozen into
    // value commands; worker tiles never access the projection provider.
    if (m_paintCoreStrokeActive && m_projectedStampProvider) {
        const auto appendProjected = [this, &stamp, stampRx, stampRy](const QPointF &center, qreal scale, qreal rotation) {
            QTransform transform;
            transform.translate(center.x(), center.y());
            transform.rotate(rotation);
            transform.scale(scale * m_projectedStrokeScale, scale * m_projectedStrokeScale);
            transform.translate(-stampRx - 0.5, -stampRy - 0.5);
            const auto patches = m_projectedStampProvider(stamp, transform);
            for (const auto &patch : patches)
                m_paintCommandStream.appendCoveragePatch(patch.first, patch.second);
        };
        if (!strokeRandom.sprayEnabled) {
            for (int index = 0; index < symmetryCenters.size(); ++index)
                appendProjected(symmetryCenters.at(index), 1.0,
                                symmetryRotations.value(index, strokeRandom.baseAngleDegrees));
        } else {
            const qreal spread = qMax<qreal>(2.0, radiusX)
                * (strokeRandom.sprayRangePercent / 100.0) * m_projectedStrokeScale;
            const int count = qMax(1, qRound(strokeRandom.sprayDensity * 0.25));
            const qreal concentration = 0.5 + strokeRandom.sprayCenterDensityPercent / 200.0;
            for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
                for (int particleIndex = 0; particleIndex < count; ++particleIndex) {
                    const qreal angle = random01(symmetryIndex, particleIndex, 0) * 2.0 * M_PI;
                    const qreal distance = std::pow(random01(symmetryIndex, particleIndex, 1), concentration) * spread;
                    const qreal sizeError = (random01(symmetryIndex, particleIndex, 2) * 2.0 - 1.0)
                        * (strokeRandom.sprayParticleRandomSizePercent / 100.0);
                    const qreal pixels = qMax<qreal>(1.0, strokeRandom.sprayParticleSizePixels * (1.0 + sizeError));
                    const qreal scale = qBound<qreal>(0.03,
                        pixels / qMax<qreal>(1.0, qMax(stampRx, stampRy)), 2.0);
                    const qreal rotation = strokeRandom.baseAngleDegrees + strokeRandom.sprayParticleRotationDegrees
                        + (random01(symmetryIndex, particleIndex, 3) * 2.0 - 1.0)
                            * strokeRandom.sprayParticleRandomRotationDegrees
                        + (random01(symmetryIndex, particleIndex, 4) * 2.0 - 1.0)
                            * strokeRandom.randomAngleDegrees;
                    const QPointF particle = symmetryCenters.at(symmetryIndex)
                        + QPointF(std::cos(angle) * distance, std::sin(angle) * distance);
                    appendProjected(particle, scale, rotation);
                }
            }
        }
        if (!m_deferPaintCoreSubmit) submitPaintCoreTiles();
        return;
    }

    // The legacy compositor remains the authority during migration, but it no
    // longer owns input resampling: every resolved symmetry/tiling centre is
    // also recorded exactly once in the core command stream. A future CPU
    // TileStore and the UV/GPU preview will consume these same commands.
    if (!strokeRandom.sprayEnabled) {
        for (int index = 0; index < symmetryCenters.size(); ++index) {
            m_paintCommandStream.append(symmetryCenters.at(index), pressure, radiusX, radiusY, finalAlpha,
                                        symmetryRotations.value(index, strokeRandom.baseAngleDegrees));
        }
    } else {
        // Spray resolves to ordinary immutable particle dabs; it has no
        // specialised compositor after this point.
        const qreal spread = qMax<qreal>(2.0, radiusX)
                            * (strokeRandom.sprayRangePercent / 100.0);
        const int count = qMax(1, qRound(strokeRandom.sprayDensity * 0.25));
        const qreal concentration = 0.5 + strokeRandom.sprayCenterDensityPercent / 200.0;
        for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
            const QPointF &center = symmetryCenters.at(symmetryIndex);
            for (int particleIndex = 0; particleIndex < count; ++particleIndex) {
                const qreal angle = random01(symmetryIndex, particleIndex, 0) * 2.0 * M_PI;
                const qreal distance = std::pow(random01(symmetryIndex, particleIndex, 1), concentration) * spread;
                const qreal sizeError = (random01(symmetryIndex, particleIndex, 2) * 2.0 - 1.0)
                                        * (strokeRandom.sprayParticleRandomSizePercent / 100.0);
                const qreal particlePixels = qMax<qreal>(1.0,
                    strokeRandom.sprayParticleSizePixels * (1.0 + sizeError));
                const qreal scale = qBound<qreal>(0.03,
                    particlePixels / qMax<qreal>(1.0, qMax(stampRx, stampRy)), 2.0);
                const qreal particleRotation = strokeRandom.baseAngleDegrees
                    + strokeRandom.sprayParticleRotationDegrees
                    + (random01(symmetryIndex, particleIndex, 3) * 2.0 - 1.0)
                        * strokeRandom.sprayParticleRandomRotationDegrees
                    + (random01(symmetryIndex, particleIndex, 4) * 2.0 - 1.0)
                        * strokeRandom.randomAngleDegrees;
                m_paintCommandStream.append(center + QPointF(std::cos(angle) * distance,
                                                              std::sin(angle) * distance),
                                            pressure, radiusX * scale, radiusY * scale, dabAlpha,
                                            particleRotation);
            }
        }
    }

    if (m_paintCoreStrokeActive) {
        if (!m_deferPaintCoreSubmit) submitPaintCoreTiles();
        return;
    }

    // The async path is intentionally restricted to the ordinary 2D coverage
    // compositor. Projected/GPU, masks, textured tips, sprays and alpha-lock
    // retain their established specialised paths until each has an equivalent
    // value-only snapshot producer. The snapshots below include the resolved
    // brush tip, flow-derived alpha cap and symmetry/tiling transforms.
    const bool canPrepareAsync2d = m_nonAccumulatingStrokeActive
        && !m_projectedStampProvider && !m_maskPaintingEnabled
        && !m_useTextureTip && !strokeRandom.sprayEnabled
        && strokeRandom.randomAngleDegrees == 0
        && m_strokeTransparencyReferenceImage.isNull() && !hasSelectionRegion();
    if (canPrepareAsync2d) {
        AsyncDabSnapshot snapshot;
        snapshot.centers = std::move(symmetryCenters);
        snapshot.tip = stamp.copy();
        snapshot.radiusX = stampRx;
        snapshot.radiusY = stampRy;
        snapshot.alphaCap = qBound(1, static_cast<int>(std::round(finalAlpha * 255.0)), 255);
        enqueueAsync2dDab(std::move(snapshot));
        return;
    }

    if (m_nonAccumulatingStrokeActive) {
        if ((!m_projectedStampProvider || !m_experimentalGpuStrokeActive)
            && m_strokeOverlayImage.isNull()) {
            return;
        }

        QColor maskColor(Qt::white);
        maskColor.setAlphaF(cachedDabAlphaF);
        const quint64 maskStampKey = makeBrushStampKey(stampRx,
                                                         stampRy,
                                                         stampHardness,
                                                         maskColor.rgba(),
                                                         useTextureStamp,
                                                        m_tipTextureToken);
        auto maskIt = m_brushStampCache.constFind(maskStampKey);
        if (maskIt == m_brushStampCache.constEnd()) {
            if (m_brushStampCache.size() > 512) {
                m_brushStampCache.clear();
                m_brushStampMaxAlphaCache.clear();
            }
            const QImage maskStamp = makeBrushStampImage(stampRx, stampRy, stampHardness, maskColor);
            maskIt = m_brushStampCache.insert(maskStampKey, maskStamp);
        }
        const QImage &maskStamp = maskIt.value();

        // Soft tips deliberately start with a low per-dab flow, but their
        // eventual ceiling is still the user-selected brush opacity.  Texture
        // tips retain their own intrinsic alpha ceiling.
        int textureAlphaCap = qBound(1, static_cast<int>(std::round(finalAlpha * 255.0)), 255);
        if (useTextureStamp) {
            auto capIt = m_brushStampMaxAlphaCache.constFind(maskStampKey);
            if (capIt == m_brushStampMaxAlphaCache.constEnd()) {
                int maxAlpha = 0;
                for (int y = 0; y < maskStamp.height(); ++y) {
                    const QRgb *row = reinterpret_cast<const QRgb *>(maskStamp.constScanLine(y));
                    for (int x = 0; x < maskStamp.width(); ++x) {
                        maxAlpha = qMax(maxAlpha, qAlpha(row[x]));
                    }
                }
                capIt = m_brushStampMaxAlphaCache.insert(maskStampKey, maxAlpha);
            }
            textureAlphaCap = capIt.value();
        }

        QVector<QRect> changedRects;
        changedRects.reserve(qMax(4, symmetryCenters.size()));
        const auto recordChangedRect = [this, &changedRects](const QRect &rect) {
            if (rect.isEmpty()) return;
            if (m_projectedStampProvider) {
                changedRects.push_back(rect);
                return;
            }
            // Merge only touching dabs. Distant symmetry copies must remain
            // separate; their bounding union can otherwise span most of a 4K
            // canvas and dominate the brush cost.
            QRect pending = rect.adjusted(-1, -1, 1, 1);
            for (int i = 0; i < changedRects.size(); ++i) {
                if (changedRects.at(i).adjusted(-2, -2, 2, 2).intersects(pending)) {
                    pending = pending.united(changedRects.at(i));
                    changedRects.removeAt(i);
                    i = -1;
                }
            }
            changedRects.push_back(pending);
        };

        const auto applyCoveragePatch = [this, textureAlphaCap, &recordChangedRect]
            (const QPoint &origin, const QImage &patch) {
            if (patch.isNull()) return;
            if (m_collect2dCoverageCommands && !m_projectedStampProvider && !m_maskPaintingEnabled) {
                m_queued2dCoverageCommands.push_back({origin, patch, textureAlphaCap});
                return;
            }
            QElapsedTimer coverageTimer;
            const bool profile2d = !m_projectedStampProvider;
            if (profile2d) coverageTimer.start();
            const bool grayscaleCoverage = !m_projectedStampProvider && !m_maskPaintingEnabled;
            if (m_strokeOverlayImage.isNull()) {
                const QImage::Format maskFormat = grayscaleCoverage
                    ? QImage::Format_Grayscale8 : QImage::Format_ARGB32_Premultiplied;
                m_strokeOverlayImage = QImage(m_strokeBaseImage.size(), maskFormat);
                m_strokeOverlayImage.fill(0);
            }
            const QRect rect(origin, patch.size());
            const QRect clipped = rect.intersected(m_strokeOverlayImage.rect());
            // All 2D stamp paths apply the selection as a QPainter clip before
            // arriving here. Rechecking QRegion::contains for every pixel is
            // especially costly for tiled spray and symmetry.
            const bool selectionAlreadyClipped = !m_projectedStampProvider && hasSelectionRegion();
            const QRect selectedBounds = selectionAlreadyClipped ? m_selectionClipRegion.boundingRect() : QRect();
            bool changed = false;
            if (grayscaleCoverage) {
                for (int row = clipped.top(); row <= clipped.bottom(); ++row) {
                    uchar *coverage = m_strokeOverlayImage.scanLine(row);
                    const QRgb *source = reinterpret_cast<const QRgb *>(patch.constScanLine(row - origin.y()));
                    for (int column = clipped.left(); column <= clipped.right(); ++column) {
                        if (!selectionAlreadyClipped && hasSelectionRegion()
                            && !m_selectionClipRegion.contains(QPoint(column, row))) continue;
                        const int sourceAlpha = qAlpha(source[column - origin.x()]);
                    if (sourceAlpha <= 0) continue;
                        const int previousAlpha = coverage[column];
                        const int nextAlpha = qMin(textureAlphaCap,
                            sourceAlpha + ((previousAlpha * (255 - sourceAlpha) + 127) / 255));
                        if (nextAlpha > previousAlpha) {
                            coverage[column] = static_cast<uchar>(nextAlpha);
                            changed = true;
                        }
                    }
                }
            } else for (int row = clipped.top(); row <= clipped.bottom(); ++row) {
                QRgb *coverage = reinterpret_cast<QRgb *>(m_strokeOverlayImage.scanLine(row));
                const QRgb *source = reinterpret_cast<const QRgb *>(patch.constScanLine(row - origin.y()));
                for (int column = clipped.left(); column <= clipped.right(); ++column) {
                    if (!selectionAlreadyClipped && hasSelectionRegion()
                        && !m_selectionClipRegion.contains(QPoint(column, row))) continue;
                    const int sourceAlpha = qAlpha(source[column - origin.x()]);
                    if (sourceAlpha <= 0) continue;
                    const int previousAlpha = qAlpha(coverage[column]);
                    const int nextAlpha = qMin(textureAlphaCap,
                        sourceAlpha + ((previousAlpha * (255 - sourceAlpha) + 127) / 255));
                    if (nextAlpha > previousAlpha) {
                        coverage[column] = qRgba(nextAlpha, nextAlpha, nextAlpha, nextAlpha);
                        changed = true;
                    }
                }
            }
            if (changed) recordChangedRect(selectionAlreadyClipped
                                                ? clipped.intersected(selectedBounds) : clipped);
            if (changed && m_projectedStrokeObserverActive && m_projectedStrokeObserver) {
                m_projectedStrokeObserver({ProjectedStrokeEvent::Phase::Coverage, clipped.topLeft(),
                                           m_strokeOverlayImage.copy(clipped),
                                           m_brushInkColor, m_tool == Tool::Eraser});
            }
            if (profile2d) m_2dPerfCoverageNs += coverageTimer.nsecsElapsed();
        };

        auto applyFirstHitStamp = [this, &strokeRandom, &maskStamp, stampRx, stampRy, &applyCoveragePatch, &recordChangedRect](const QPointF &center,
                                                         qreal opacityScale,
                                                         qreal scale,
                                                         qreal angleOffset) {
            if (opacityScale <= 0.0) {
                return;
            }

            if (m_projectedStampProvider) {
                QTransform transform;
                transform.translate(center.x(), center.y());
                transform.rotate(strokeRandom.baseAngleDegrees + angleOffset);
                transform.scale(scale * strokeRandom.projectedScale, scale * strokeRandom.projectedScale);
                transform.translate(-stampRx - 0.5, -stampRy - 0.5);
                QElapsedTimer projectedCoverageTimer;
                projectedCoverageTimer.start();
                const auto patches = m_projectedStampProvider(maskStamp, transform);
                const qint64 projectionMs = projectedCoverageTimer.elapsed();
                QVector<QPair<QPoint, QImage>> paddedPatches;
                paddedPatches.reserve(patches.size());
                for (const auto &patch : patches) {
                    if (m_uvClipRegion.isEmpty()) {
                        applyCoveragePatch(patch.first, patch.second);
                        continue;
                    }
                    const QImage padded = ProjectedBrush::padCoverage(patch.first, patch.second, m_projectedUvInteriorRegion);
                    paddedPatches.push_back({patch.first - QPoint(1, 1), padded});
                }
                for (const auto &patch : ProjectedBrush::mergeCoverage(paddedPatches, m_documentSize))
                    applyCoveragePatch(patch.first, patch.second);
                const qint64 coveragePostprocessMs = projectedCoverageTimer.elapsed() - projectionMs;
                static QElapsedTimer lastProjectedCoverageReport;
                if (projectionMs + coveragePostprocessMs >= 16
                    && (!lastProjectedCoverageReport.isValid() || lastProjectedCoverageReport.elapsed() >= 1000)) {
                    QString message;
                    QDebug(&message) << "[BrushPerf] projectedCoverageMs=" << projectionMs
                                     << "paddingMergeMs=" << coveragePostprocessMs
                                     << "patches=" << patches.size();
                    BrushPerformance::report(message);
                    lastProjectedCoverageReport.start();
                }
                return;
            }

            const qreal scaledRx = (stampRx + 1.0) * std::abs(scale);
            const qreal scaledRy = (stampRy + 1.0) * std::abs(scale);
            const qreal bound = std::sqrt(scaledRx * scaledRx + scaledRy * scaledRy) + 3.0;

            const int left = qMax(0, static_cast<int>(std::floor(center.x() - bound)));
            const int top = qMax(0, static_cast<int>(std::floor(center.y() - bound)));
            const int right = qMin(m_strokeOverlayImage.width() - 1, static_cast<int>(std::ceil(center.x() + bound)));
            const int bottom = qMin(m_strokeOverlayImage.height() - 1, static_cast<int>(std::ceil(center.y() + bound)));
            if (right < left || bottom < top) {
                return;
            }

            const QRect rect(left, top, right - left + 1, bottom - top + 1);
            // With no rotation, scaling, clip or subpixel placement, the
            // cached stamp already is the coverage patch. Avoid allocating an
            // ARGB image and drawing an identical copy through QPainter.
            const qreal integralX = std::round(center.x());
            const qreal integralY = std::round(center.y());
            const bool directCachedStamp = !m_projectedStampProvider
                                           && !m_externalUvStrokeActive
                                           && !hasSelectionRegion()
                                           && qFuzzyIsNull(strokeRandom.baseAngleDegrees + angleOffset)
                                           && qFuzzyCompare(scale, 1.0)
                                           && qFuzzyCompare(center.x() + 1.0, integralX + 1.0)
                                           && qFuzzyCompare(center.y() + 1.0, integralY + 1.0);
            if (directCachedStamp) {
                applyCoveragePatch(QPoint(static_cast<int>(integralX) - stampRx,
                                          static_cast<int>(integralY) - stampRy), maskStamp);
                return;
            }
            QImage dabPatch(rect.size(), QImage::Format_ARGB32_Premultiplied);
            dabPatch.fill(Qt::transparent);

            QPainter dabPainter(&dabPatch);
            if (!dabPainter.isActive()) {
                return;
            }
            dabPainter.setRenderHint(QPainter::Antialiasing, m_tipAntiAliasingEnabled);
            dabPainter.setRenderHint(QPainter::SmoothPixmapTransform, m_tipAntiAliasingEnabled);
            dabPainter.setPen(Qt::NoPen);

            if (m_externalUvStrokeActive && !m_uvClipRegion.isEmpty()) {
                QRegion localClip = m_externalUvIslandClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                if (m_externalUvFaceSelectionActive) {
                    const QRegion faceLocal = m_externalUvFaceClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                    localClip = localClip.intersected(faceLocal);
                }
                if (hasSelectionRegion()) {
                    const QRegion selectionLocal = m_selectionClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                    localClip = localClip.intersected(selectionLocal);
                }
                if (localClip.isEmpty()) {
                    return;
                }
                dabPainter.setClipRegion(localClip, Qt::IntersectClip);
            } else if (hasSelectionRegion()) {
                QRegion localClip = m_selectionClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                if (localClip.isEmpty()) {
                    return;
                }
                dabPainter.setClipRegion(localClip, Qt::IntersectClip);
            }

            dabPainter.translate(center.x() - rect.left(), center.y() - rect.top());
            dabPainter.rotate(strokeRandom.baseAngleDegrees + angleOffset);
            dabPainter.setOpacity(qBound(0.0, opacityScale, 1.0));
            dabPainter.scale(scale, scale);
            dabPainter.drawImage(QPointF(-stampRx, -stampRy), maskStamp);
            dabPainter.end();

            applyCoveragePatch(rect.topLeft(), dabPatch);
        };

        struct SprayParticle {
            QPointF center;
            qreal scale = 1.0;
            qreal rotation = 0.0;
        };
        // The 2D spray path used to allocate and merge a coverage image for
        // every particle.  A normal spray event has up to 64 particles, so
        // that also meant scanning the overlay and lock images up to 64 times.
        // Merge particles only when their enclosing patch is economical; a
        // very wide spray would otherwise turn this into a large empty scan.
        const auto apply2dSprayPatch = [this, &strokeRandom, &maskStamp, stampRx, stampRy,
                                        &applyCoveragePatch]
            (const QVector<SprayParticle> &particles) {
            if (particles.isEmpty()) return;

            const QRect documentRect = m_strokeOverlayImage.rect();
            const auto particleRect = [&particles, stampRx, stampRy](int index) {
                const SprayParticle &particle = particles.at(index);
                const qreal scaledRx = (stampRx + 1.0) * std::abs(particle.scale);
                const qreal scaledRy = (stampRy + 1.0) * std::abs(particle.scale);
                const qreal bound = std::sqrt(scaledRx * scaledRx + scaledRy * scaledRy) + 3.0;
                return QRect(static_cast<int>(std::floor(particle.center.x() - bound)),
                             static_cast<int>(std::floor(particle.center.y() - bound)),
                             static_cast<int>(std::ceil(bound * 2.0)) + 1,
                             static_cast<int>(std::ceil(bound * 2.0)) + 1);
            };
            const auto renderPatch = [this, &particles, &strokeRandom, &maskStamp, stampRx, stampRy,
                                      &applyCoveragePatch](const QRect &rect, const QVector<int> &indices) {
                if (rect.isEmpty() || indices.isEmpty()) return;
                QImage sprayPatch(rect.size(), QImage::Format_ARGB32_Premultiplied);
                sprayPatch.fill(Qt::transparent);
                QPainter painter(&sprayPatch);
                if (!painter.isActive()) return;
                painter.setRenderHint(QPainter::Antialiasing, m_tipAntiAliasingEnabled);
                painter.setRenderHint(QPainter::SmoothPixmapTransform, m_tipAntiAliasingEnabled);
                painter.setPen(Qt::NoPen);
                if (m_externalUvStrokeActive && !m_uvClipRegion.isEmpty()) {
                    QRegion localClip = m_externalUvIslandClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                    if (m_externalUvFaceSelectionActive)
                        localClip = localClip.intersected(m_externalUvFaceClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top()));
                    if (hasSelectionRegion())
                        localClip = localClip.intersected(m_selectionClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top()));
                    if (localClip.isEmpty()) return;
                    painter.setClipRegion(localClip, Qt::IntersectClip);
                } else if (hasSelectionRegion()) {
                    const QRegion localClip = m_selectionClipRegion.intersected(QRegion(rect)).translated(-rect.left(), -rect.top());
                    if (localClip.isEmpty()) return;
                    painter.setClipRegion(localClip, Qt::IntersectClip);
                }
                for (const int index : indices) {
                    const SprayParticle &particle = particles.at(index);
                    painter.save();
                    painter.translate(particle.center.x() - rect.left(), particle.center.y() - rect.top());
                    painter.rotate(strokeRandom.baseAngleDegrees + particle.rotation);
                    painter.scale(particle.scale, particle.scale);
                    painter.drawImage(QPointF(-stampRx, -stampRy), maskStamp);
                    painter.restore();
                }
                painter.end();
                applyCoveragePatch(rect.topLeft(), sprayPatch);
            };

            qreal minX = std::numeric_limits<qreal>::max();
            qreal minY = std::numeric_limits<qreal>::max();
            qreal maxX = std::numeric_limits<qreal>::lowest();
            qreal maxY = std::numeric_limits<qreal>::lowest();
            qreal individualArea = 0.0;
            for (const SprayParticle &particle : particles) {
                const qreal scaledRx = (stampRx + 1.0) * std::abs(particle.scale);
                const qreal scaledRy = (stampRy + 1.0) * std::abs(particle.scale);
                const qreal bound = std::sqrt(scaledRx * scaledRx + scaledRy * scaledRy) + 3.0;
                minX = qMin(minX, particle.center.x() - bound);
                minY = qMin(minY, particle.center.y() - bound);
                maxX = qMax(maxX, particle.center.x() + bound);
                maxY = qMax(maxY, particle.center.y() + bound);
                individualArea += 4.0 * bound * bound;
            }
            const QRect rect(qMax(0, static_cast<int>(std::floor(minX))),
                             qMax(0, static_cast<int>(std::floor(minY))),
                             qMin(m_strokeOverlayImage.width() - 1, static_cast<int>(std::ceil(maxX)))
                                 - qMax(0, static_cast<int>(std::floor(minX))) + 1,
                             qMin(m_strokeOverlayImage.height() - 1, static_cast<int>(std::ceil(maxY)))
                                 - qMax(0, static_cast<int>(std::floor(minY))) + 1);
            const qreal patchArea = static_cast<qreal>(rect.width()) * rect.height();
            constexpr qreal kMaxMergedPatchArea = 512.0 * 512.0;
            QVector<int> allIndices;
            allIndices.reserve(particles.size());
            for (int index = 0; index < particles.size(); ++index) allIndices.push_back(index);
            if (rect.isEmpty()) return;
            if (patchArea <= kMaxMergedPatchArea && patchArea <= individualArea * 2.0) {
                ++m_2dPerfMergedPatches;
                renderPatch(rect, allIndices);
                return;
            }

            // Wide spray used to fall back to one QImage + coverage scan per
            // particle. Split it into bounded spatial tiles instead, so each
            // tile keeps local particle batching without scanning the empty
            // area between distant symmetry copies.
            constexpr int kSprayTileSize = 256;
            QHash<QPoint, QVector<int>> tileParticles;
            for (int index = 0; index < particles.size(); ++index) {
                const QRect bounds = particleRect(index).intersected(documentRect);
                if (bounds.isEmpty()) continue;
                for (int y = bounds.top() / kSprayTileSize; y <= bounds.bottom() / kSprayTileSize; ++y)
                    for (int x = bounds.left() / kSprayTileSize; x <= bounds.right() / kSprayTileSize; ++x)
                        tileParticles[QPoint(x, y)].push_back(index);
            }
            for (auto it = tileParticles.cbegin(); it != tileParticles.cend(); ++it) {
                const QRect tileRect(it.key() * kSprayTileSize, QSize(kSprayTileSize, kSprayTileSize));
                QRect tightRect;
                for (const int index : it.value()) {
                    const QRect clipped = particleRect(index).intersected(tileRect).intersected(documentRect);
                    tightRect = tightRect.isNull() ? clipped : tightRect.united(clipped);
                }
                if (tightRect.isEmpty()) continue;
                ++m_2dPerfTiledPatches;
                renderPatch(tightRect, it.value());
            }
        };

        if (!strokeRandom.sprayEnabled) {
            // Use the same context-retained provider as spray.  The provider
            // still composites each dab immediately; it only batches GL
            // context ownership, so the normal live preview remains exact.
            if (m_projectedStampProvider && m_projectedStampBatchProvider) {
                QVector<ProjectedStampInstance> instances;
                instances.reserve(symmetryCenters.size());
                for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
                    const QPointF &center = symmetryCenters.at(symmetryIndex);
                    const qreal randomAngle = (random01(symmetryIndex, 0, 0) * 2.0 - 1.0)
                                             * strokeRandom.randomAngleDegrees;
                    QTransform transform;
                    transform.translate(center.x(), center.y());
                    transform.rotate(strokeRandom.baseAngleDegrees + randomAngle);
                    transform.scale(strokeRandom.projectedScale, strokeRandom.projectedScale);
                    transform.translate(-stampRx - 0.5, -stampRy - 0.5);
                    instances.push_back({maskStamp, transform});
                }
                const auto patches = m_collectProjectedEventInstances
                    ? (m_projectedEventInstances += instances, QVector<QPair<QPoint, QImage>>())
                    : m_projectedStampBatchProvider(instances);
                QVector<QPair<QPoint, QImage>> paddedPatches;
                paddedPatches.reserve(patches.size());
                for (const auto &patch : patches) {
                    if (m_uvClipRegion.isEmpty()) applyCoveragePatch(patch.first, patch.second);
                    else paddedPatches.push_back({patch.first - QPoint(1, 1),
                        ProjectedBrush::padCoverage(patch.first, patch.second, m_projectedUvInteriorRegion)});
                }
                for (const auto &patch : ProjectedBrush::mergeCoverage(paddedPatches, m_documentSize))
                    applyCoveragePatch(patch.first, patch.second);
            } else {
                for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
                    const QPointF &center = symmetryCenters.at(symmetryIndex);
                    const qreal randomAngle = (random01(symmetryIndex, 0, 0) * 2.0 - 1.0)
                                             * strokeRandom.randomAngleDegrees;
                    applyFirstHitStamp(center, 1.0, 1.0, randomAngle);
                }
            }
        } else {
            const qreal spread = qMax<qreal>(2.0, radiusX)
                                * (strokeRandom.sprayRangePercent / 100.0)
                                * (m_projectedStampProvider ? strokeRandom.projectedScale : 1.0);
            const int count = qMax(1, qRound(strokeRandom.sprayDensity * 0.25));
            if (!m_projectedStampProvider)
                m_2dPerfSprayParticles += static_cast<quint64>(symmetryCenters.size()) * count;
            QVector<ProjectedStampInstance> sprayInstances;
            if (m_projectedStampProvider && m_projectedStampBatchProvider)
                sprayInstances.reserve(symmetryCenters.size() * count);
            // Keep every 2D symmetry copy in one spatial batch.  Per-centre
            // batching duplicated tile setup and coverage passes even when
            // neighbouring copies landed in the same tile.
            QVector<SprayParticle> twoDSprayParticles;
            if (!m_projectedStampProvider)
                twoDSprayParticles.reserve(symmetryCenters.size() * count);
            for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
                const QPointF &center = symmetryCenters.at(symmetryIndex);
                for (int i = 0; i < count; ++i) {
                    const qreal angle = random01(symmetryIndex, i, 0) * 2.0 * M_PI;
                    const qreal randomRadius = random01(symmetryIndex, i, 1);
                    // Map a uniform random value to area, then apply only a
                    // gentle optional centre bias.  The old exponent started
                    // at 1.0, which already concentrates particles toward the
                    // centre and turns a small density increase into a line.
                    const qreal concentration = 0.5 + strokeRandom.sprayCenterDensityPercent / 200.0;
                    const qreal distance = std::pow(randomRadius, concentration) * spread;
                    const qreal sizeError = (random01(symmetryIndex, i, 2) * 2.0 - 1.0)
                                            * (strokeRandom.sprayParticleRandomSizePercent / 100.0);
                    const qreal particlePixels = qMax<qreal>(1.0, strokeRandom.sprayParticleSizePixels * (1.0 + sizeError));
                    const qreal particleScale = qBound<qreal>(0.03,
                        particlePixels / qMax<qreal>(1.0, qMax(stampRx, stampRy)), 2.0);
                    const qreal particleRotation = strokeRandom.sprayParticleRotationDegrees
                                                    + (random01(symmetryIndex, i, 3) * 2.0 - 1.0)
                                                          * strokeRandom.sprayParticleRandomRotationDegrees
                                                    + (random01(symmetryIndex, i, 4) * 2.0 - 1.0)
                                                          * strokeRandom.randomAngleDegrees;
                    const QPointF particleCenter = center + QPointF(std::cos(angle) * distance,
                                                                      std::sin(angle) * distance);
                    if (m_projectedStampProvider && m_projectedStampBatchProvider) {
                        QTransform transform;
                        transform.translate(particleCenter.x(), particleCenter.y());
                        transform.rotate(strokeRandom.baseAngleDegrees + particleRotation);
                        transform.scale(particleScale * strokeRandom.projectedScale,
                                        particleScale * strokeRandom.projectedScale);
                        transform.translate(-stampRx - 0.5, -stampRy - 0.5);
                        sprayInstances.push_back({maskStamp, transform});
                    } else if (!m_projectedStampProvider) {
                        twoDSprayParticles.push_back({particleCenter, particleScale, particleRotation});
                    } else {
                        applyFirstHitStamp(particleCenter, 1.0, particleScale, particleRotation);
                    }
                }
            }
            if (!m_projectedStampProvider)
                apply2dSprayPatch(twoDSprayParticles);
            if (!sprayInstances.isEmpty()) {
                const auto patches = m_collectProjectedEventInstances
                    ? (m_projectedEventInstances += sprayInstances, QVector<QPair<QPoint, QImage>>())
                    : m_projectedStampBatchProvider(sprayInstances);
                QVector<QPair<QPoint, QImage>> paddedPatches;
                paddedPatches.reserve(patches.size());
                for (const auto &patch : patches) {
                    if (m_uvClipRegion.isEmpty()) {
                        applyCoveragePatch(patch.first, patch.second);
                    } else {
                        const QImage padded = ProjectedBrush::padCoverage(
                            patch.first, patch.second, m_projectedUvInteriorRegion);
                        paddedPatches.push_back({patch.first - QPoint(1, 1), padded});
                    }
                }
                for (const auto &patch : ProjectedBrush::mergeCoverage(paddedPatches, m_documentSize))
                    applyCoveragePatch(patch.first, patch.second);
            }
        }

        if (changedRects.isEmpty()) {
            return;
        }

        if (m_defer2dPreviewComposite && !m_projectedStampProvider) {
            for (const QRect &changedRect : std::as_const(changedRects))
                m_deferred2dPreviewRegion += changedRect;
            return;
        }

        if (m_strokeBaseImage.isNull() || m_strokeOverlayImage.isNull() || m_strokePreviewLayerImage.isNull()) {
            return;
        }

        const bool erasingPixels = !m_maskPaintingEnabled && m_tool == Tool::Eraser;
        const QColor strokeTint = m_maskPaintingEnabled
            ? QColor(qGray(color.rgb()), qGray(color.rgb()), qGray(color.rgb()), color.alpha())
            : m_brushInkColor;
        const int tintR = strokeTint.red(), tintG = strokeTint.green(), tintB = strokeTint.blue();
        const bool restrictToOpaquePixels = !m_strokeTransparencyReferenceImage.isNull()
            && m_strokeTransparencyReferenceImage.size() == m_strokePreviewLayerImage.size();
        for (const QRect &changedRect : std::as_const(changedRects)) {
            const QRect dirtyRect = changedRect.intersected(m_strokeOverlayImage.rect());
            if (dirtyRect.isEmpty()) continue;
            if (m_projectedStampProvider) {
                m_strokeDirtyRect = m_strokeDirtyRect.isNull() ? dirtyRect : m_strokeDirtyRect.united(dirtyRect);
                for (int row = dirtyRect.top() / 128; row <= dirtyRect.bottom() / 128; ++row)
                    for (int column = dirtyRect.left() / 128; column <= dirtyRect.right() / 128; ++column)
                        m_strokeDirtyTiles.insert(QPoint(column,row));
                m_pendingCompositeDirtyRect = m_pendingCompositeDirtyRect.isNull()
                    ? dirtyRect : m_pendingCompositeDirtyRect.united(dirtyRect);
                if (m_incrementalCompositeCacheActive)
                    m_pendingProjectedCompositeRegion += dirtyRect;
            }
            for (int y = dirtyRect.top(); y <= dirtyRect.bottom(); ++y) {
                    QRgb *preview = reinterpret_cast<QRgb *>(m_strokePreviewLayerImage.scanLine(y)) + dirtyRect.left();
                    const QRgb *base = reinterpret_cast<const QRgb *>(m_strokeBaseImage.constScanLine(y)) + dirtyRect.left();
                    const bool grayscaleCoverage = m_strokeOverlayImage.format() == QImage::Format_Grayscale8;
                    const uchar *coverage8 = grayscaleCoverage
                        ? m_strokeOverlayImage.constScanLine(y) + dirtyRect.left() : nullptr;
                    const QRgb *coverage = grayscaleCoverage ? nullptr
                        : reinterpret_cast<const QRgb *>(m_strokeOverlayImage.constScanLine(y)) + dirtyRect.left();
                    uchar *maskPreview = m_maskPaintingEnabled && !m_maskStrokePreviewImage.isNull()
                        ? m_maskStrokePreviewImage.scanLine(y) + dirtyRect.left() : nullptr;
                    const QRgb *reference = restrictToOpaquePixels
                        ? reinterpret_cast<const QRgb *>(m_strokeTransparencyReferenceImage.constScanLine(y)) + dirtyRect.left() : nullptr;
                    for (int x = 0; x < dirtyRect.width(); ++x) {
                        int sourceA = grayscaleCoverage ? coverage8[x] : qAlpha(coverage[x]);
                        if (reference) sourceA = (sourceA * qAlpha(reference[x]) + 127) / 255;
                        const int inverseA = 255 - sourceA;
                        const int outR = erasingPixels
                                             ? (qRed(base[x]) * inverseA + 127) / 255
                                             : (tintR * sourceA + qRed(base[x]) * inverseA + 127) / 255;
                        const int outG = erasingPixels
                                             ? (qGreen(base[x]) * inverseA + 127) / 255
                                             : (tintG * sourceA + qGreen(base[x]) * inverseA + 127) / 255;
                        const int outB = erasingPixels
                                             ? (qBlue(base[x]) * inverseA + 127) / 255
                                             : (tintB * sourceA + qBlue(base[x]) * inverseA + 127) / 255;
                        const int outA = erasingPixels
                                             ? (qAlpha(base[x]) * inverseA + 127) / 255
                                             : sourceA + (qAlpha(base[x]) * inverseA + 127) / 255;
                        preview[x] = qRgba(outR, outG, outB, outA);
                        if (maskPreview) maskPreview[x] = static_cast<uchar>(outR);
                    }
            }
            if (m_projectedStampProvider && m_projectedCompositeObserver && !m_maskPaintingEnabled
                && !restrictToOpaquePixels) {
                m_projectedCompositeObserver(m_strokeBaseImage.copy(dirtyRect),
                                              m_strokeOverlayImage.copy(dirtyRect),
                                              m_strokePreviewLayerImage.copy(dirtyRect),
                                              strokeTint, erasingPixels);
            }
        }

        bumpContentRevision();
        return;
    }

    QPainter *painter = m_activeExternalBatchPainter;
    QPainter localPainter;
    if (!painter) {
        QImage *layerImage = activeLayerImage();
        if (!layerImage) {
            return;
        }
        localPainter.begin(layerImage);
        localPainter.setRenderHint(QPainter::Antialiasing, m_tipAntiAliasingEnabled);
        localPainter.setRenderHint(QPainter::SmoothPixmapTransform, m_tipAntiAliasingEnabled);
        localPainter.setPen(Qt::NoPen);
        if (m_externalUvStrokeActive && !m_uvClipRegion.isEmpty()) {
            QRegion clip = m_externalUvIslandClipRegion;
            if (m_externalUvFaceSelectionActive) {
                clip = clip.intersected(m_externalUvFaceClipRegion);
            }
            if (hasSelectionRegion()) {
                clip = clip.intersected(m_selectionClipRegion);
            }
            if (clip.isEmpty()) {
                localPainter.end();
                return;
            }
            localPainter.setClipRegion(clip, Qt::IntersectClip);
        } else if (hasSelectionRegion()) {
            if (m_selectionClipRegion.isEmpty()) {
                localPainter.end();
                return;
            }
            localPainter.setClipRegion(m_selectionClipRegion, Qt::IntersectClip);
        }
        painter = &localPainter;
    }

    auto drawStampAt = [painter, &stamp, stampRx, stampRy, this, &strokeRandom](const QPointF &center, qreal opacityScale, qreal scale, qreal angleOffset) {
        if (m_strokeTransparencyReferenceImage.isNull()) {
            painter->save();
            if (!m_maskPaintingEnabled && m_tool == Tool::Eraser) {
                painter->setCompositionMode(QPainter::CompositionMode_DestinationOut);
            }
            painter->translate(center);
            painter->rotate(strokeRandom.baseAngleDegrees + angleOffset);
            painter->setOpacity(qBound(0.0, opacityScale, 1.0));
            painter->scale(scale, scale);
            painter->drawImage(QPointF(-stampRx, -stampRy), stamp);
            painter->restore();
            return;
        }

        const qreal scaledRx = (stampRx + 1.0) * std::abs(scale);
        const qreal scaledRy = (stampRy + 1.0) * std::abs(scale);
        const qreal bound = std::sqrt(scaledRx * scaledRx + scaledRy * scaledRy) + 3.0;

        const int left = qMax(0, static_cast<int>(std::floor(center.x() - bound)));
        const int top = qMax(0, static_cast<int>(std::floor(center.y() - bound)));
        const int right = qMin(m_strokeTransparencyReferenceImage.width() - 1, static_cast<int>(std::ceil(center.x() + bound)));
        const int bottom = qMin(m_strokeTransparencyReferenceImage.height() - 1, static_cast<int>(std::ceil(center.y() + bound)));
        if (right < left || bottom < top) {
            return;
        }

        const QRect rect(left, top, right - left + 1, bottom - top + 1);
        QImage dabPatch(rect.size(), QImage::Format_ARGB32_Premultiplied);
        dabPatch.fill(Qt::transparent);

        QPainter dabPainter(&dabPatch);
        if (!dabPainter.isActive()) {
            return;
        }
        dabPainter.setRenderHint(QPainter::Antialiasing, m_tipAntiAliasingEnabled);
        dabPainter.setRenderHint(QPainter::SmoothPixmapTransform, m_tipAntiAliasingEnabled);
        dabPainter.setPen(Qt::NoPen);
        dabPainter.translate(center.x() - rect.left(), center.y() - rect.top());
        dabPainter.rotate(strokeRandom.baseAngleDegrees + angleOffset);
        dabPainter.setOpacity(qBound(0.0, opacityScale, 1.0));
        dabPainter.scale(scale, scale);
        dabPainter.drawImage(QPointF(-stampRx, -stampRy), stamp);
        dabPainter.end();

        for (int y = 0; y < rect.height(); ++y) {
            QRgb *dst = reinterpret_cast<QRgb *>(dabPatch.scanLine(y));
            const QRgb *ref = reinterpret_cast<const QRgb *>(m_strokeTransparencyReferenceImage.constScanLine(rect.top() + y)) + rect.left();
            for (int x = 0; x < rect.width(); ++x) {
                const int refA = qAlpha(ref[x]);
                if (refA <= 0) {
                    dst[x] = qRgba(0, 0, 0, 0);
                    continue;
                }
                if (refA >= 255) {
                    continue;
                }
                const int r = (qRed(dst[x]) * refA + 127) / 255;
                const int g = (qGreen(dst[x]) * refA + 127) / 255;
                const int b = (qBlue(dst[x]) * refA + 127) / 255;
                const int a = (qAlpha(dst[x]) * refA + 127) / 255;
                dst[x] = qRgba(r, g, b, a);
            }
        }

        painter->save();
        if (!m_maskPaintingEnabled && m_tool == Tool::Eraser) {
            painter->setCompositionMode(QPainter::CompositionMode_DestinationOut);
        }
        painter->drawImage(rect.topLeft(), dabPatch);
        painter->restore();
    };

    if (!strokeRandom.sprayEnabled) {
        for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
            const QPointF &center = symmetryCenters.at(symmetryIndex);
            const qreal randomAngle = (random01(symmetryIndex, 0, 0) * 2.0 - 1.0)
                                     * strokeRandom.randomAngleDegrees;
            drawStampAt(center, 1.0, 1.0, randomAngle);
        }
    } else {
        const qreal spread = qMax<qreal>(2.0, radiusX)
                            * (strokeRandom.sprayRangePercent / 100.0);
        const int count = qMax(1, qRound(strokeRandom.sprayDensity * 0.25));
        for (int symmetryIndex = 0; symmetryIndex < symmetryCenters.size(); ++symmetryIndex) {
            const QPointF &center = symmetryCenters.at(symmetryIndex);
            for (int i = 0; i < count; ++i) {
                const qreal angle = random01(symmetryIndex, i, 0) * 2.0 * M_PI;
                const qreal randomRadius = random01(symmetryIndex, i, 1);
                const qreal concentration = 0.5 + strokeRandom.sprayCenterDensityPercent / 200.0;
                const qreal distance = std::pow(randomRadius, concentration) * spread;
                const qreal sizeError = (random01(symmetryIndex, i, 2) * 2.0 - 1.0)
                                        * (strokeRandom.sprayParticleRandomSizePercent / 100.0);
                const qreal particlePixels = qMax<qreal>(1.0, strokeRandom.sprayParticleSizePixels * (1.0 + sizeError));
                const qreal particleScale = qBound<qreal>(0.03,
                    particlePixels / qMax<qreal>(1.0, qMax(stampRx, stampRy)), 2.0);
                const qreal particleRotation = strokeRandom.sprayParticleRotationDegrees
                                               + (random01(symmetryIndex, i, 3) * 2.0 - 1.0)
                                                     * strokeRandom.sprayParticleRandomRotationDegrees
                                               + (random01(symmetryIndex, i, 4) * 2.0 - 1.0)
                                                     * strokeRandom.randomAngleDegrees;
                drawStampAt(center + QPointF(std::cos(angle) * distance,
                                              std::sin(angle) * distance), 1.0, particleScale, particleRotation);
            }
        }
    }

    if (localPainter.isActive()) {
        localPainter.end();
    }

    bumpContentRevision();
}

void DrawingCanvas::scheduleDeferred2dStrokePreview()
{
    if (m_deferred2dPreviewRegion.isEmpty() || m_2dPreviewFrameTimer.isActive()) {
        return;
    }
    m_2dPreviewFrameTimer.start();
}

void DrawingCanvas::enqueueAsync2dDab(AsyncDabSnapshot snapshot)
{
    snapshot.generation = m_async2dGeneration;
    snapshot.sequence = m_async2dNextSequence++;
    m_async2dPending.enqueue(std::move(snapshot));
    startNextAsync2dDab();
}

void DrawingCanvas::startNextAsync2dDab()
{
    if (m_async2dWorkerBusy || m_async2dPending.isEmpty()) return;
    // One future per dab made large brushes spend disproportionate time in
    // thread-pool scheduling and signal delivery. A small ordered batch keeps
    // the same sequence barrier while amortising that fixed cost.
    constexpr int kMaxSnapshotsPerWorkerJob = 12;
    QVector<AsyncDabSnapshot> snapshots;
    snapshots.reserve(qMin(kMaxSnapshotsPerWorkerJob, m_async2dPending.size()));
    while (!m_async2dPending.isEmpty() && snapshots.size() < kMaxSnapshotsPerWorkerJob)
        snapshots.push_back(m_async2dPending.dequeue());
    m_async2dWorkerBusy = true;
    // The worker turns a copied tip and copied transform centres into wholly
    // independent patches.  It intentionally has no canvas/document pointer.
    m_async2dWatcher.setFuture(QtConcurrent::run([snapshots = std::move(snapshots)] {
        QVector<AsyncDabResult> results;
        results.reserve(snapshots.size());
        for (const AsyncDabSnapshot &snapshot : snapshots) {
            AsyncDabResult result;
            result.generation = snapshot.generation;
            result.sequence = snapshot.sequence;
            result.commands.reserve(snapshot.centers.size());
            for (const QPointF &center : snapshot.centers) {
                const QPoint origin(qRound(center.x()) - snapshot.radiusX,
                                    qRound(center.y()) - snapshot.radiusY);
                result.commands.push_back({origin, snapshot.tip.copy(), snapshot.alphaCap});
            }
            results.push_back(std::move(result));
        }
        return results;
    }));
}

void DrawingCanvas::acceptAsync2dDab(AsyncDabResult result)
{
    if (result.generation != m_async2dGeneration
        || result.sequence < m_async2dNextCommitSequence) return;
    m_async2dReady.insert(result.sequence, std::move(result));
    commitReadyAsync2dDabs();
}

void DrawingCanvas::commitReadyAsync2dDabs()
{
    bool committed = false;
    while (true) {
        auto it = m_async2dReady.find(m_async2dNextCommitSequence);
        if (it == m_async2dReady.end()) break;
        for (const CoveragePatchCommand &command : std::as_const(it->commands))
            m_queued2dCoverageCommands.push_back(command);
        m_async2dReady.erase(it);
        ++m_async2dNextCommitSequence;
        committed = true;
    }
    if (!committed) return;
    flushQueued2dCoverageCommands();
    scheduleDeferred2dStrokePreview();
}

void DrawingCanvas::finishAsync2dStroke()
{
    // Mouse-up is the ordering barrier: commit every command of this
    // generation before the preview becomes the undoable layer image.
    while (m_async2dWorkerBusy) {
        m_async2dWatcher.future().waitForFinished();
        m_async2dWorkerBusy = false;
        for (AsyncDabResult &result : m_async2dWatcher.result()) acceptAsync2dDab(std::move(result));
        startNextAsync2dDab();
    }
    commitReadyAsync2dDabs();
}

void DrawingCanvas::invalidateAsync2dDabs()
{
    m_paintTileCoordinator.cancel();
    ++m_async2dGeneration;
    m_async2dNextSequence = 0;
    m_async2dNextCommitSequence = 0;
    m_async2dPending.clear();
    m_async2dReady.clear();
}

void DrawingCanvas::submitPaintCoreTiles(bool force)
{
    if (!m_paintCoreStrokeActive || m_paintTileCoordinator.isBusy()
        || m_paintCommandStream.commands().size() <= m_paintCoreSubmittedCommandCount) return;
    const int firstPending = m_paintCoreSubmittedCommandCount;
    const int totalCommands = m_paintCommandStream.commands().size();
    // Keep the first mark immediate. Afterwards, extremely small tails mostly
    // pay QFuture/task and tile setup overhead, so coalesce briefly while
    // preserving an upper latency bound well below one display frame.
    constexpr int kMinCommandsBeforeImmediateSubmit = 8;
    constexpr int kSubmitCoalesceMs = 4;
    if (!force && firstPending > 0 && totalCommands - firstPending < kMinCommandsBeforeImmediateSubmit) {
        if (!m_paintCoreSubmitCoalesceQueued) {
            m_paintCoreSubmitCoalesceQueued = true;
            const quint64 generation = m_paintCommandGeneration;
            QTimer::singleShot(kSubmitCoalesceMs, this, [this, generation] {
                m_paintCoreSubmitCoalesceQueued = false;
                if (m_paintCoreStrokeActive && generation == m_paintCommandGeneration)
                    submitPaintCoreTiles(true);
            });
        }
        return;
    }
    // Bound worker latency under tablet/input bursts. The unfinished tail stays
    // in the canonical stream and is submitted by commitPaintCoreTiles() in
    // strict sequence, while mouse-up drains all remaining batches.
    constexpr int kMaxCommandsPerTileBatch = 64;
    const QVector<PaintCore::DabCommand> pending = m_paintCommandStream.commands().mid(
        firstPending, kMaxCommandsPerTileBatch);
    const int committedThrough = firstPending + pending.size();
    BrushPerformance::report(QStringLiteral("[PaintPath] core-submit generation=%1 newCommands=%2 committedThrough=%3 totalCommands=%4")
        .arg(m_paintCommandGeneration).arg(pending.size()).arg(committedThrough).arg(totalCommands));
    m_paintTileCoordinator.submit(m_paintCommandStream.snapshot(), pending, m_documentSize,
                                  PaintCore::kDefaultTileSize, committedThrough);
}

void DrawingCanvas::commitPaintCoreTiles(const PaintTileCoordinator::BatchResult &result)
{
    if (!m_paintCoreStrokeActive || result.generation != m_paintCommandGeneration
        || m_strokeOverlayImage.isNull()
        || (m_strokeOverlayImage.format() != QImage::Format_Grayscale8
            && m_strokeOverlayImage.format() != QImage::Format_ARGB32_Premultiplied)) return;
    for (const PaintCore::TileResult &tile : result.tiles) {
        const QPoint origin(tile.key.x * PaintCore::kDefaultTileSize,
                            tile.key.y * PaintCore::kDefaultTileSize);
        const QRect target(origin, tile.coverage.size());
        const QRect clipped = target.intersected(m_strokeOverlayImage.rect());
        if (clipped.isEmpty()) continue;
        const bool grayscaleOverlay = m_strokeOverlayImage.format() == QImage::Format_Grayscale8;
        for (int y = 0; y < clipped.height(); ++y) {
            const uchar *source = tile.coverage.constScanLine(clipped.top() + y - origin.y())
                + clipped.left() - origin.x();
            const int opacityCap = qBound(0, qRound(m_paintCommandStream.snapshot().opacity * 255.0), 255);
            if (grayscaleOverlay) {
                uchar *destination = m_strokeOverlayImage.scanLine(clipped.top() + y) + clipped.left();
                for (int x = 0; x < clipped.width(); ++x)
                    destination[x] = uchar(qMin(opacityCap,
                        source[x] + (destination[x] * (255 - source[x]) + 127) / 255));
            } else {
                QRgb *destination = reinterpret_cast<QRgb *>(m_strokeOverlayImage.scanLine(clipped.top() + y))
                    + clipped.left();
                for (int x = 0; x < clipped.width(); ++x) {
                    const int previous = qAlpha(destination[x]);
                    const int alpha = qMin(opacityCap,
                        source[x] + (previous * (255 - source[x]) + 127) / 255);
                    destination[x] = qRgba(0, 0, 0, alpha);
                }
            }
        }
        m_deferred2dPreviewRegion += clipped;
        if (m_projectedStampProvider) {
            m_strokeDirtyRect = m_strokeDirtyRect.isNull() ? clipped : m_strokeDirtyRect.united(clipped);
            m_pendingCompositeDirtyRect = m_pendingCompositeDirtyRect.isNull()
                ? clipped : m_pendingCompositeDirtyRect.united(clipped);
            for (int row = clipped.top() / PaintCore::kDefaultTileSize;
                 row <= clipped.bottom() / PaintCore::kDefaultTileSize; ++row)
                for (int column = clipped.left() / PaintCore::kDefaultTileSize;
                     column <= clipped.right() / PaintCore::kDefaultTileSize; ++column)
                    m_strokeDirtyTiles.insert(QPoint(column, row));
            if (m_incrementalCompositeCacheActive) m_pendingProjectedCompositeRegion += clipped;
        }
    }
    m_paintCoreSubmittedCommandCount = qMax(m_paintCoreSubmittedCommandCount, result.commandCount);
    BrushPerformance::report(QStringLiteral("[PaintPath] core-ready generation=%1 commands=%2 tiles=%3")
        .arg(result.generation).arg(result.commandCount).arg(result.tiles.size()));
    scheduleDeferred2dStrokePreview();
    // Commands may have arrived while this batch was executing. The next
    // batch contains only commands appended since this commit. UI-side
    // source-over composition preserves the exact stroke accumulation without
    // replaying the full stream for every input packet.
    submitPaintCoreTiles();
}

void DrawingCanvas::finishPaintCoreStroke()
{
    // A completion can observe commands appended while its worker ran and
    // schedule one newer full-stream batch. Keep flushing until that final
    // snapshot has reached the overlay before the stroke becomes undoable.
    do {
        submitPaintCoreTiles(true);
        m_paintTileCoordinator.flush();
    } while (m_paintTileCoordinator.isBusy()
             || m_paintCoreSubmittedCommandCount < m_paintCommandStream.commands().size());
    BrushPerformance::report(QStringLiteral("[PaintPath] core-tile-commit commands=%1")
        .arg(m_paintCoreSubmittedCommandCount));
}

void DrawingCanvas::flushQueued2dCoverageCommands()
{
    if (m_queued2dCoverageCommands.isEmpty() || m_strokeOverlayImage.isNull()) return;
    QElapsedTimer timer;
    timer.start();
    constexpr int kTileSize = 128;
    QHash<QPoint, QVector<int>> tileCommands;
    for (int i = 0; i < m_queued2dCoverageCommands.size(); ++i) {
        const CoveragePatchCommand &command = m_queued2dCoverageCommands.at(i);
        const QRect clipped(command.origin, command.patch.size());
        const QRect bounds = clipped.intersected(m_strokeOverlayImage.rect());
        if (bounds.isEmpty()) continue;
        for (int y = bounds.top() / kTileSize; y <= bounds.bottom() / kTileSize; ++y)
            for (int x = bounds.left() / kTileSize; x <= bounds.right() / kTileSize; ++x)
                tileCommands[QPoint(x, y)].push_back(i);
    }
    for (auto it = tileCommands.cbegin(); it != tileCommands.cend(); ++it) {
        const QRect tile(it.key() * kTileSize, QSize(kTileSize, kTileSize));
        const QRect dirty = tile.intersected(m_strokeOverlayImage.rect());
        bool changed = false;
        for (const int index : it.value()) {
            const CoveragePatchCommand &command = m_queued2dCoverageCommands.at(index);
            const QRect bounds(command.origin, command.patch.size());
            const QRect clipped = bounds.intersected(dirty);
            for (int y = clipped.top(); y <= clipped.bottom(); ++y) {
                uchar *coverage = m_strokeOverlayImage.scanLine(y);
                const QRgb *source = reinterpret_cast<const QRgb *>(command.patch.constScanLine(y - command.origin.y()));
                for (int x = clipped.left(); x <= clipped.right(); ++x) {
                    const int sourceAlpha = qAlpha(source[x - command.origin.x()]);
                    if (sourceAlpha <= 0) continue;
                    const int previous = coverage[x];
                    const int next = qMin(command.alphaCap, sourceAlpha + ((previous * (255 - sourceAlpha) + 127) / 255));
                    if (next > previous) { coverage[x] = static_cast<uchar>(next); changed = true; }
                }
            }
        }
        if (changed) m_deferred2dPreviewRegion += dirty;
    }
    m_queued2dCoverageCommands.clear();
    m_2dPerfCoverageNs += timer.nsecsElapsed();
    bumpContentRevision();
}

void DrawingCanvas::flushDeferred2dStrokePreview()
{
    const QRegion regions = m_deferred2dPreviewRegion;
    m_deferred2dPreviewRegion = QRegion();
    if (regions.isEmpty() || m_strokeBaseImage.isNull() || m_strokeOverlayImage.isNull()
        || m_strokePreviewLayerImage.isNull()) {
        return;
    }

    QElapsedTimer previewTimer;
    previewTimer.start();

    const bool erasingPixels = !m_maskPaintingEnabled && m_tool == Tool::Eraser;
    const QColor strokeTint = m_maskPaintingEnabled
        ? QColor(m_tool == Tool::Eraser ? 0 : m_brushInkColor.lightness(),
                 m_tool == Tool::Eraser ? 0 : m_brushInkColor.lightness(),
                 m_tool == Tool::Eraser ? 0 : m_brushInkColor.lightness())
        : m_brushInkColor;
    const int tintR = strokeTint.red(), tintG = strokeTint.green(), tintB = strokeTint.blue();
    const bool restrictToOpaquePixels = !m_strokeTransparencyReferenceImage.isNull()
        && m_strokeTransparencyReferenceImage.size() == m_strokePreviewLayerImage.size();
    for (const QRect &changedRect : regions) {
        const QRect dirtyRect = changedRect.intersected(m_strokeOverlayImage.rect());
        if (dirtyRect.isEmpty()) continue;
        for (int y = dirtyRect.top(); y <= dirtyRect.bottom(); ++y) {
            QRgb *preview = reinterpret_cast<QRgb *>(m_strokePreviewLayerImage.scanLine(y)) + dirtyRect.left();
            const QRgb *base = reinterpret_cast<const QRgb *>(m_strokeBaseImage.constScanLine(y)) + dirtyRect.left();
            const bool grayscaleCoverage = m_strokeOverlayImage.format() == QImage::Format_Grayscale8;
            const uchar *coverage8 = grayscaleCoverage
                ? m_strokeOverlayImage.constScanLine(y) + dirtyRect.left() : nullptr;
            const QRgb *coverage = grayscaleCoverage ? nullptr
                : reinterpret_cast<const QRgb *>(m_strokeOverlayImage.constScanLine(y)) + dirtyRect.left();
            uchar *maskPreview = m_maskPaintingEnabled && !m_maskStrokePreviewImage.isNull()
                ? m_maskStrokePreviewImage.scanLine(y) + dirtyRect.left() : nullptr;
            const QRgb *reference = restrictToOpaquePixels
                ? reinterpret_cast<const QRgb *>(m_strokeTransparencyReferenceImage.constScanLine(y)) + dirtyRect.left() : nullptr;
            for (int x = 0; x < dirtyRect.width(); ++x) {
                int sourceA = grayscaleCoverage ? coverage8[x] : qAlpha(coverage[x]);
                if (reference) sourceA = (sourceA * qAlpha(reference[x]) + 127) / 255;
                const int inverseA = 255 - sourceA;
                const int outR = erasingPixels ? (qRed(base[x]) * inverseA + 127) / 255
                    : (tintR * sourceA + qRed(base[x]) * inverseA + 127) / 255;
                const int outG = erasingPixels ? (qGreen(base[x]) * inverseA + 127) / 255
                    : (tintG * sourceA + qGreen(base[x]) * inverseA + 127) / 255;
                const int outB = erasingPixels ? (qBlue(base[x]) * inverseA + 127) / 255
                    : (tintB * sourceA + qBlue(base[x]) * inverseA + 127) / 255;
                const int outA = erasingPixels ? (qAlpha(base[x]) * inverseA + 127) / 255
                    : sourceA + (qAlpha(base[x]) * inverseA + 127) / 255;
                preview[x] = qRgba(outR, outG, outB, outA);
                if (maskPreview) maskPreview[x] = static_cast<uchar>(outR);
            }
        }
    }
    m_2dPerfPreviewNs += previewTimer.nsecsElapsed();
    bumpContentRevision();
}

quint64 DrawingCanvas::makeBrushStampKey(int radiusX,
                                         int radiusY,
                                         int hardnessPercent,
                                         QRgb colorRgba,
                                         bool textureTip,
                                         quint32 textureToken) const
{
    quint64 key = 1469598103934665603ull;
    const auto mix = [&key](quint64 value) {
        key ^= value + 0x9e3779b97f4a7c15ull + (key << 6) + (key >> 2);
    };

    mix(static_cast<quint64>(qBound(0, radiusX, 4095)));
    mix(static_cast<quint64>(qBound(0, radiusY, 4095)));
    mix(static_cast<quint64>(qBound(0, hardnessPercent, 100)));
    mix(static_cast<quint64>(colorRgba));
    mix(textureTip ? 1ull : 0ull);
    mix(static_cast<quint64>(textureToken));
    return key;
}

QImage DrawingCanvas::makeBrushStampImage(int radiusX, int radiusY, int hardnessPercent, const QColor &color) const
{
    const int rx = qMax(1, radiusX);
    const int ry = qMax(1, radiusY);
    const int w = rx * 2 + 2;
    const int h = ry * 2 + 2;
    const QPointF center(rx + 0.5, ry + 0.5);

    QImage image(w, h, QImage::Format_ARGB32_Premultiplied);
    image.fill(Qt::transparent);

    if (m_useTextureTip && !m_tipTextureImage.isNull()) {
        QImage mask = m_tipTextureImage.scaled(w, h, Qt::IgnoreAspectRatio, Qt::SmoothTransformation)
                          .convertToFormat(QImage::Format_ARGB32);
        const bool sourceHasAlpha = mask.hasAlphaChannel();
        const qreal hardnessNorm = qBound(0.01, hardnessPercent / 100.0, 1.0);
        const qreal gamma = 1.0 + (1.0 - hardnessNorm) * 2.5;
        const int srcR = color.red();
        const int srcG = color.green();
        const int srcB = color.blue();
        const int srcA = color.alpha();

        for (int y = 0; y < h; ++y) {
            QRgb *dst = reinterpret_cast<QRgb *>(image.scanLine(y));
            const QRgb *src = reinterpret_cast<const QRgb *>(mask.constScanLine(y));
            for (int x = 0; x < w; ++x) {
                const int alpha = qAlpha(src[x]);
                const int luminance = qGray(src[x]);
                // Prefer alpha-driven masks when available; RGB luminance is only a fallback for no-alpha sources.
                qreal a = sourceHasAlpha
                              ? (alpha / 255.0)
                              : (1.0 - (luminance / 255.0));
                if (a <= 0.0) {
                    dst[x] = qRgba(0, 0, 0, 0);
                    continue;
                }
                a = std::pow(a, gamma);
                const int outA = qBound(0, static_cast<int>(std::round(srcA * a)), 255);
                const int outR = (srcR * outA + 127) / 255;
                const int outG = (srcG * outA + 127) / 255;
                const int outB = (srcB * outA + 127) / 255;
                dst[x] = qRgba(outR, outG, outB, outA);
            }
        }

        return image;
    }

    QPainter p(&image);
    p.setRenderHint(QPainter::Antialiasing, m_tipAntiAliasingEnabled);
    p.setPen(Qt::NoPen);
    p.save();
    p.translate(center);
    p.scale(rx, ry);

    if (hardnessPercent >= 100) {
        p.setBrush(color);
        p.drawEllipse(QPointF(0.0, 0.0), 1.0, 1.0);
    } else {
        const qreal hardStop = qBound(0.0, hardnessPercent / 100.0, 0.99);
        QRadialGradient gradient(0.0, 0.0, 1.0);
        QColor edge = color;
        edge.setAlpha(0);
        const auto falloffColor = [&color](qreal normalizedDistance) {
            // A quadratic tail keeps very soft tips visible far from the centre.
            // The former linear ramp looked like a soft marker; this is closer to
            // the broad, low-density falloff of an airbrush while remaining the
            // exact same brush tip used by every brush mode.
            QColor result = color;
            const qreal coverage = 1.0 - normalizedDistance * normalizedDistance;
            result.setAlphaF(color.alphaF() * qBound(0.0, coverage, 1.0));
            return result;
        };
        gradient.setColorAt(0.0, color);
        gradient.setColorAt(hardStop, color);
        const qreal feather = 1.0 - hardStop;
        gradient.setColorAt(hardStop + feather * 0.25, falloffColor(0.25));
        gradient.setColorAt(hardStop + feather * 0.50, falloffColor(0.50));
        gradient.setColorAt(hardStop + feather * 0.75, falloffColor(0.75));
        gradient.setColorAt(1.0, edge);
        p.setBrush(gradient);
        p.drawEllipse(QPointF(0.0, 0.0), 1.0, 1.0);
    }

    p.restore();
    return image;
}

qreal DrawingCanvas::brushStep(qreal pressure) const
{
    const qreal sizeFactor = sizePressureFactor(pressure);
    const qreal effectiveSize = qMax(1.0, m_baseBrushSize * sizeFactor);
    const qreal hardness = qBound(0.0, m_hardnessPercent / 100.0, 1.0);
    // Photoshop-compatible spacing: the value is the distance between dab
    // centres as a percentage of the current brush-tip diameter.  It is an
    // artist setting, not an automatic overlap cap.
    Q_UNUSED(hardness);
    qreal step = qMax(0.5, effectiveSize * (m_spacingPercent / 100.0));
    if (m_isDrawing && m_strokeRandom.sprayEnabled) {
        // Spray emits smaller, distance-spaced particle packets rather than
        // one visibly separated burst at every ordinary brush dab.
        step = qMax(0.5, step * 0.25);
    }
    return step;
}


qreal DrawingCanvas::pressureCurveValue(const QVector<qreal> &curve, qreal pressure) const
{
    if (curve.size() < 2) {
        return qBound(0.0, pressure, 1.0);
    }

    const qreal p = qBound(0.0, pressure, 1.0);
    const int segments = curve.size() - 1;
    const qreal scaled = p * segments;
    const int i0 = qBound(0, static_cast<int>(std::floor(scaled)), segments - 1);
    const int i1 = i0 + 1;
    const qreal t = qBound(0.0, scaled - i0, 1.0);
    const qreal v0 = qBound(0.0, curve[i0], 1.0);
    const qreal v1 = qBound(0.0, curve[i1], 1.0);
    return qBound(0.0, v0 + (v1 - v0) * t, 1.0);
}

qreal DrawingCanvas::sizePressureFactor(qreal pressure) const
{
    if (!m_pressureSizeEnabled) {
        return 1.0;
    }
    const qreal minFactor = qBound(0.0, m_pressureSizeMinPercent / 100.0, 1.0);
    const qreal curveValue = pressureCurveValue(m_pressureSizeCurve, pressure);
    return minFactor + (1.0 - minFactor) * curveValue;
}

qreal DrawingCanvas::opacityPressureFactor(qreal pressure) const
{
    if (!m_pressureOpacityEnabled) {
        return 1.0;
    }
    const qreal minFactor = qBound(0.0, m_pressureOpacityMinPercent / 100.0, 1.0);
    const qreal curveValue = pressureCurveValue(m_pressureOpacityCurve, pressure);
    return minFactor + (1.0 - minFactor) * curveValue;
}
void DrawingCanvas::ensureLayers()
{
    if (!m_layers.isEmpty()) {
        return;
    }

    setDocumentSize(m_documentSize);
}

void DrawingCanvas::bumpContentRevision()
{
    ++m_contentRevision;
}

DrawingCanvas::HistoryState DrawingCanvas::captureHistoryState() const
{
    HistoryState state;
    state.layers = m_layers;
    state.activeLayerIndex = m_activeLayerIndex;
    state.documentSize = m_documentSize;
    state.selectionPath = m_selectionPathCanvas;
    state.selectionRegion = m_selectionClipRegion;
    state.hasSelection = m_hasSelectionRegion;
    return state;
}

void DrawingCanvas::beginHistoryTransaction(const QString &actionLabel)
{
    if (m_historyTransactionActive) {
        return;
    }
    m_historyTransactionActive = true;
    pushUndoHistoryState(actionLabel);
}

void DrawingCanvas::endHistoryTransaction()
{
    m_historyTransactionActive = false;
}

void DrawingCanvas::pushUndoHistoryState(const QString &actionLabel)
{
    ensureLayers();
    HistoryState state = captureHistoryState();
    state.actionLabel = actionLabel;
    const int redoBeforeClear = m_redoHistory.size();
    m_undoHistory.push_back(state);
    while (m_undoHistory.size() > m_maxHistoryEntries) {
        m_undoHistory.remove(0);
    }
    m_redoHistory.clear();
    trimUndoHistoryMemory();
    const RasterLayer *activeLayer = (state.activeLayerIndex >= 0 && state.activeLayerIndex < state.layers.size())
                                         ? &state.layers.at(state.activeLayerIndex)
                                         : nullptr;
    qInfo().noquote()
        << "[History] PUSH"
        << "action=" << (actionLabel.isEmpty() ? QStringLiteral("<unlabeled>") : actionLabel)
        << "undo=" << m_undoHistory.size()
        << "redoCleared=" << redoBeforeClear
        << "revision=" << m_contentRevision
        << "layer=" << state.activeLayerIndex
        << "name=" << (activeLayer ? activeLayer->name : QStringLiteral("<none>"))
        << "imageKey=" << (activeLayer ? QString::number(activeLayer->image.cacheKey()) : QStringLiteral("0"))
        << "layers=" << state.layers.size()
        << "selection=" << state.hasSelection;
}

void DrawingCanvas::restoreFromHistoryState(const HistoryState &state)
{
    QString currentLayerId;
    if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        currentLayerId = m_layers[m_activeLayerIndex].layerId;
    }

    m_layers = state.layers;
    m_documentSize = state.documentSize;
    if (m_layers.isEmpty()) {
        setDocumentSize(m_documentSize);
        return;
    }

    int preferredIndex = -1;
    if (!currentLayerId.trimmed().isEmpty()) {
        for (int i = 0; i < m_layers.size(); ++i) {
            if (m_layers[i].layerId == currentLayerId && !isGroupLayerType(m_layers[i].type)) {
                preferredIndex = i;
                break;
            }
        }
    }
    m_activeLayerIndex = (preferredIndex >= 0)
                            ? preferredIndex
                            : qBound(0, state.activeLayerIndex, m_layers.size() - 1);
    m_isDrawing = false;
    m_externalUvStrokeActive = false;
    m_strokeDirtyRect = QRect();
    m_strokeDirtyTiles.clear();
    m_pendingProjectedSegment = false;
    m_projectedSliceBudget = -1;
    m_projectedStampProvider = {};
    m_projectedStrokeScale = 1.0;
    m_projectedSpacingScale = 1.0;
    m_nonAccumulatingStrokeActive = false;
    m_distanceToNextStamp = 0.0;
    m_strokeBaseImage = QImage();
    m_strokeOverlayImage = QImage();
    m_strokePreviewLayerImage = QImage();
    m_maskStrokePreviewImage = QImage();
    m_selectionDragActive = false;
    m_selectionPolylineBuilding = false;
    m_selectionWorkingPoints.clear();
    m_selectionTranslationActive = false;
    m_selectionTranslationMovePixels = false;
    m_selectionTranslationUndoPrimed = false;
    m_selectionTranslationOffset = QPoint(0, 0);
    m_selectionTranslationBaseRegion = QRegion();
    m_selectionTranslationBasePath = QPainterPath();
    m_selectionTranslationBaseLayerImage = QImage();
    m_selectionTranslationBackgroundImage = QImage();
    m_selectionTranslationCutoutImage = QImage();
    m_selectionTranslationLayerIndex = -1;
    m_layerTranslationActive = false;
    m_layerTranslationAnchorCanvasPoint = QPointF();
    m_layerTranslationOffset = QPoint(0, 0);
    m_layerTranslationLayerIndex = -1;
    m_layerTranslationBaseLayerImage = QImage();
    m_layerTranslationUndoPrimed = false;

    const bool prevSelection = hasSelectionRegion();
    m_selectionPathCanvas = state.selectionPath;
    m_selectionClipRegion = state.selectionRegion.intersected(QRegion(QRect(QPoint(0, 0), m_documentSize)));
    m_hasSelectionRegion = state.hasSelection && !m_selectionClipRegion.isEmpty() && !m_selectionPathCanvas.isEmpty();
    if (!m_hasSelectionRegion) {
        m_selectionPathCanvas = QPainterPath();
        m_selectionClipRegion = QRegion();
    }
    if (isFreeTransformMode() && m_selectionToolEnabled && m_hasSelectionRegion) {
        refreshFreeTransformSession();
    }

    rebuildUvClipRegion();
    updateSelectionAntsAnimationState();
    if (onSelectionRegionChanged && prevSelection != m_hasSelectionRegion) {
        onSelectionRegionChanged(m_hasSelectionRegion);
    }
    resize(m_documentSize);
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
}

bool DrawingCanvas::canUndo() const
{
    return !m_undoHistory.isEmpty();
}

bool DrawingCanvas::canRedo() const
{
    return !m_redoHistory.isEmpty();
}

bool DrawingCanvas::undo()
{
    invalidateAsync2dDabs();
    if (m_undoHistory.isEmpty()) {
        qInfo().noquote() << "[History] UNDO blocked: stack empty";
        return false;
    }
    const QString actionLabel = m_undoHistory.constLast().actionLabel;
    HistoryState current = captureHistoryState();
    current.actionLabel = actionLabel;
    m_redoHistory.push_back(current);
    const HistoryState state = m_undoHistory.takeLast();
    const RasterLayer *currentLayer = (current.activeLayerIndex >= 0 && current.activeLayerIndex < current.layers.size())
                                          ? &current.layers.at(current.activeLayerIndex)
                                          : nullptr;
    const RasterLayer *targetLayer = (state.activeLayerIndex >= 0 && state.activeLayerIndex < state.layers.size())
                                         ? &state.layers.at(state.activeLayerIndex)
                                         : nullptr;
    qInfo().noquote()
        << "[History] UNDO begin"
        << "action=" << (actionLabel.isEmpty() ? QStringLiteral("<unlabeled>") : actionLabel)
        << "currentKey=" << (currentLayer ? QString::number(currentLayer->image.cacheKey()) : QStringLiteral("0"))
        << "targetKey=" << (targetLayer ? QString::number(targetLayer->image.cacheKey()) : QStringLiteral("0"))
        << "layer=" << state.activeLayerIndex
        << "name=" << (targetLayer ? targetLayer->name : QStringLiteral("<none>"));
    restoreFromHistoryState(state);
    qInfo().noquote() << "[History] UNDO end"
                      << "action=" << (actionLabel.isEmpty() ? QStringLiteral("<unlabeled>") : actionLabel)
                      << "undo=" << m_undoHistory.size()
                      << "redo=" << m_redoHistory.size()
                      << "revision=" << m_contentRevision;
    return true;
}

bool DrawingCanvas::redo()
{
    invalidateAsync2dDabs();
    if (m_redoHistory.isEmpty()) {
        qInfo().noquote() << "[History] REDO blocked: stack empty";
        return false;
    }
    const QString actionLabel = m_redoHistory.constLast().actionLabel;
    HistoryState current = captureHistoryState();
    current.actionLabel = actionLabel;
    m_undoHistory.push_back(current);
    const HistoryState state = m_redoHistory.takeLast();
    const RasterLayer *currentLayer = (current.activeLayerIndex >= 0 && current.activeLayerIndex < current.layers.size())
                                          ? &current.layers.at(current.activeLayerIndex)
                                          : nullptr;
    const RasterLayer *targetLayer = (state.activeLayerIndex >= 0 && state.activeLayerIndex < state.layers.size())
                                         ? &state.layers.at(state.activeLayerIndex)
                                         : nullptr;
    qInfo().noquote()
        << "[History] REDO begin"
        << "action=" << (actionLabel.isEmpty() ? QStringLiteral("<unlabeled>") : actionLabel)
        << "currentKey=" << (currentLayer ? QString::number(currentLayer->image.cacheKey()) : QStringLiteral("0"))
        << "targetKey=" << (targetLayer ? QString::number(targetLayer->image.cacheKey()) : QStringLiteral("0"))
        << "layer=" << state.activeLayerIndex
        << "name=" << (targetLayer ? targetLayer->name : QStringLiteral("<none>"));
    restoreFromHistoryState(state);
    qInfo().noquote() << "[History] REDO end"
                      << "action=" << (actionLabel.isEmpty() ? QStringLiteral("<unlabeled>") : actionLabel)
                      << "undo=" << m_undoHistory.size()
                      << "redo=" << m_redoHistory.size()
                      << "revision=" << m_contentRevision;
    return true;
}

void DrawingCanvas::clearHistory()
{
    qInfo().noquote() << "[History] CLEAR"
                      << "undoRemoved=" << m_undoHistory.size()
                      << "redoRemoved=" << m_redoHistory.size()
                      << "revision=" << m_contentRevision;
    m_undoHistory.clear();
    m_redoHistory.clear();
}

void DrawingCanvas::rebuildUvClipRegion()
{
    m_uvClipRegion = QRegion();
    m_projectedUvInteriorRegion = QRegion();
    m_uvIslandRegions.clear();
    m_externalUvIslandClipRegion = QRegion();
    m_externalUvIslandIndex = -1;
    if (m_uvOverlayPoints.isEmpty() || m_uvOverlayIndices.size() < 3) {
        return;
    }

    const qreal maxX = qMax(1, m_documentSize.width() - 1);
    const qreal maxY = qMax(1, m_documentSize.height() - 1);
    const int triCount = m_uvOverlayIndices.size() / 3;
    QBitmap projectedInterior(m_documentSize);
    projectedInterior.fill(Qt::color0);
    QPainter interiorPainter(&projectedInterior);
    interiorPainter.setRenderHint(QPainter::Antialiasing, false);
    interiorPainter.setPen(Qt::NoPen);
    interiorPainter.setBrush(Qt::color1);
    QVector<int> parents(triCount);
    QVector<QRegion> triangleRegions(triCount);
    for (int triangle = 0; triangle < triCount; ++triangle) parents[triangle] = triangle;
    const auto rootOf = [&parents](int triangle) {
        while (parents[triangle] != triangle) {
            parents[triangle] = parents[parents[triangle]];
            triangle = parents[triangle];
        }
        return triangle;
    };
    QHash<QPair<quint64, quint64>, int> edgeOwners;
    const auto vertexKey = [](const QPointF &uv) {
        const quint64 horizontal = qRound64(qBound(0.0, uv.x(), 1.0) * 100000000.0);
        const quint64 vertical = qRound64(qBound(0.0, uv.y(), 1.0) * 100000000.0);
        return (horizontal << 32) | vertical;
    };
    for (int t = 0; t < triCount; ++t) {
        const quint32 i0 = m_uvOverlayIndices[t * 3 + 0];
        const quint32 i1 = m_uvOverlayIndices[t * 3 + 1];
        const quint32 i2 = m_uvOverlayIndices[t * 3 + 2];
        if (i0 >= static_cast<quint32>(m_uvOverlayPoints.size())
            || i1 >= static_cast<quint32>(m_uvOverlayPoints.size())
            || i2 >= static_cast<quint32>(m_uvOverlayPoints.size())) {
            continue;
        }

        const QPointF uv0 = m_uvOverlayPoints[static_cast<int>(i0)];
        const QPointF uv1 = m_uvOverlayPoints[static_cast<int>(i1)];
        const QPointF uv2 = m_uvOverlayPoints[static_cast<int>(i2)];
        QPolygonF projectedTriangle;
        for (const QPointF &uv : {uv0, uv1, uv2})
            projectedTriangle << QPointF(uv.x() * m_documentSize.width(), (1.0 - uv.y()) * m_documentSize.height());
        interiorPainter.drawPolygon(projectedTriangle, Qt::WindingFill);
        const QPointF p0(qBound(0.0, uv0.x(), 1.0) * maxX, (1.0 - qBound(0.0, uv0.y(), 1.0)) * maxY);
        const QPointF p1(qBound(0.0, uv1.x(), 1.0) * maxX, (1.0 - qBound(0.0, uv1.y(), 1.0)) * maxY);
        const QPointF p2(qBound(0.0, uv2.x(), 1.0) * maxX, (1.0 - qBound(0.0, uv2.y(), 1.0)) * maxY);

        QPolygon tri;
        tri << p0.toPoint() << p1.toPoint() << p2.toPoint();
        triangleRegions[t] = QRegion(tri, Qt::WindingFill);
        m_uvClipRegion = m_uvClipRegion.united(triangleRegions[t]);
        const quint64 vertices[]{vertexKey(uv0), vertexKey(uv1), vertexKey(uv2)};
        for (int edge = 0; edge < 3; ++edge) {
            const quint64 first = vertices[edge];
            const quint64 second = vertices[(edge + 1) % 3];
            if (first == second) continue;
            const auto key = qMakePair(qMin(first, second), qMax(first, second));
            const auto owner = edgeOwners.constFind(key);
            if (owner == edgeOwners.cend()) edgeOwners.insert(key, t);
            else parents[rootOf(t)] = rootOf(owner.value());
        }
    }
    interiorPainter.end();
    m_projectedUvInteriorRegion = QRegion(projectedInterior);
    QHash<int, int> islandIndices;
    for (int triangle = 0; triangle < triCount; ++triangle) {
        if (triangleRegions[triangle].isEmpty()) continue;
        const int root = rootOf(triangle);
        if (!islandIndices.contains(root)) {
            islandIndices.insert(root, m_uvIslandRegions.size());
            m_uvIslandRegions.push_back(QRegion());
        }
        QRegion &island = m_uvIslandRegions[islandIndices.value(root)];
        island = island.united(triangleRegions[triangle]);
    }

    if (!m_uvClipRegion.isEmpty()) {
        // Integer region clipping can leave 1px cracks between adjacent UV triangles.
        // Grow the region slightly so edge pixels remain paintable and no white seam appears.
        QRegion expanded = m_uvClipRegion;
        for (int dy = -1; dy <= 1; ++dy) {
            for (int dx = -1; dx <= 1; ++dx) {
                if (dx == 0 && dy == 0) {
                    continue;
                }
                expanded = expanded.united(m_uvClipRegion.translated(dx, dy));
            }
        }
        m_uvClipRegion = expanded;
    }
}

bool DrawingCanvas::updateExternalUvIsland(const QPointF &point)
{
    const QPoint pixel = point.toPoint();
    int islandIndex = -1;
    if (m_externalUvIslandIndex >= 0
        && m_uvIslandRegions[m_externalUvIslandIndex].contains(pixel)) {
        return false;
    }
    for (int index = 0; index < m_uvIslandRegions.size(); ++index) {
        if (m_uvIslandRegions[index].contains(pixel)) {
            islandIndex = index;
            break;
        }
    }
    if (islandIndex < 0) {
        const QRect neighborhood(pixel - QPoint(1, 1), QSize(3, 3));
        for (int index = 0; index < m_uvIslandRegions.size(); ++index) {
            if (m_uvIslandRegions[index].intersects(neighborhood)) {
                islandIndex = index;
                break;
            }
        }
    }
    const bool changed = islandIndex != m_externalUvIslandIndex;
    m_externalUvIslandIndex = islandIndex;
    m_externalUvIslandClipRegion = QRegion();
    if (islandIndex >= 0) {
        const QRegion &island = m_uvIslandRegions[islandIndex];
        QRegion expanded = island;
        for (int offsetY = -1; offsetY <= 1; ++offsetY) {
            for (int offsetX = -1; offsetX <= 1; ++offsetX) {
                expanded = expanded.united(island.translated(offsetX, offsetY));
            }
        }
        for (int index = 0; index < m_uvIslandRegions.size(); ++index) {
            if (index != islandIndex) expanded = expanded.subtracted(m_uvIslandRegions[index].subtracted(island));
        }
        m_externalUvIslandClipRegion = expanded;
    }
    return changed;
}

void DrawingCanvas::setSelectionPathFromPolygon(const QVector<QPointF> &points)
{
    applySelectionPolygon(points, SelectionCombineMode::Replace);
}

bool DrawingCanvas::tryHandleModifierColorSample(const QPointF &canvasPoint, Qt::KeyboardModifiers modifiers)
{
    if (!modifiers.testFlag(Qt::AltModifier)) {
        return false;
    }

    if (canSampleColorProvider && !canSampleColorProvider()) {
        return true;
    }

    const bool sampleActiveLayerOnly = modifiers.testFlag(Qt::ShiftModifier);
    QColor sampled;
    const bool sampledOk = sampleActiveLayerOnly
                               ? sampleActiveLayerColorAtCanvasPoint(canvasPoint, &sampled)
                               : sampleCompositedColorAtCanvasPoint(canvasPoint, &sampled);
    if (sampledOk && onColorSampled) {
        onColorSampled(sampled, sampleActiveLayerOnly);
    }
    return true;
}

void DrawingCanvas::trimUndoHistoryMemory()
{
    // A paint stroke detaches the edited QImage from its previous snapshot.
    // At 4K that is roughly 64 MiB per colour layer (and 8K is four times
    // that), so the old fixed 50-entry limit could make the application swap
    // after only a few strokes. Keep regular undo available, but bound the
    // unique image storage retained by history.
    constexpr qint64 kHistoryImageBudgetBytes = 256LL * 1024 * 1024;
    const auto retainedImageBytes = [this]() -> qint64 {
        QSet<quint64> seenImages;
        qint64 total = 0;
        const auto addImage = [&seenImages, &total](const QImage &image) {
            if (image.isNull()) return;
            const quint64 key = image.cacheKey();
            if (key == 0 || seenImages.contains(key)) return;
            seenImages.insert(key);
            total += image.sizeInBytes();
        };
        for (const HistoryState &state : m_undoHistory) {
            for (const RasterLayer &layer : state.layers) {
                addImage(layer.image);
                addImage(layer.maskImage);
            }
        }
        return total;
    };

    while (m_undoHistory.size() > 1 && retainedImageBytes() > kHistoryImageBudgetBytes) {
        m_undoHistory.removeFirst();
    }
}

bool DrawingCanvas::subtreeContainsTransientPreview(int index) const
{
    if (!m_nonAccumulatingStrokeActive || index < 0 || index >= m_layers.size()) {
        return false;
    }
    if (index == m_activeLayerIndex) return true;
    for (int child = 0; child < m_layers.size(); ++child) {
        if (m_layers.at(child).parentIndex == index && subtreeContainsTransientPreview(child)) {
            return true;
        }
    }
    return false;
}

quint64 DrawingCanvas::subtreeCacheSignature(int index) const
{
    if (index < 0 || index >= m_layers.size()) return 0;
    const RasterLayer &layer = m_layers.at(index);
    auto mix = [](quint64 value, quint64 part) {
        return value ^ (part + 0x9e3779b97f4a7c15ULL + (value << 6) + (value >> 2));
    };
    quint64 signature = static_cast<quint64>(qHash(layer.type));
    signature = mix(signature, static_cast<quint64>(qHash(layer.blendMode)));
    signature = mix(signature, static_cast<quint64>(layer.visible));
    signature = mix(signature, static_cast<quint64>(qRound(layer.opacityPercent * 100.0)));
    signature = mix(signature, layer.image.cacheKey());
    signature = mix(signature, layer.maskImage.cacheKey());
    signature = mix(signature, static_cast<quint64>(layer.maskEnabled));
    signature = mix(signature, static_cast<quint64>(layer.textElements.size()));
    for (const RasterLayer::TextElement &element : layer.textElements) {
        signature = mix(signature, static_cast<quint64>(qHash(element.text)));
        signature = mix(signature, static_cast<quint64>(qHash(element.fontFamily)));
        signature = mix(signature, static_cast<quint64>(qRound(element.fontPixelSize * 100.0)));
        signature = mix(signature, static_cast<quint64>(element.color.rgba()));
        signature = mix(signature, static_cast<quint64>(qRound(element.position.x() * 100.0)));
        signature = mix(signature, static_cast<quint64>(qRound(element.position.y() * 100.0)));
        signature = mix(signature, static_cast<quint64>(qRound(element.rotationDegrees * 100.0)));
        signature = mix(signature, static_cast<quint64>(element.alignment));
        signature = mix(signature, static_cast<quint64>(element.bold));
        signature = mix(signature, static_cast<quint64>(element.italic));
        signature = mix(signature, static_cast<quint64>(element.underline));
    }
    for (int child = 0; child < m_layers.size(); ++child) {
        if (m_layers.at(child).parentIndex == index) {
            signature = mix(signature, subtreeCacheSignature(child));
        }
    }
    return signature;
}

QImage DrawingCanvas::composeLayerSubtree(int index) const
{
    if (index < 0 || index >= m_layers.size() || !m_layers.at(index).visible) return QImage();
    const RasterLayer &layer = m_layers.at(index);
    QImage result(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    result.fill(Qt::transparent);
    if (isGroupLayerType(layer.type)) {
        const bool cacheEligible = layer.blendMode != QStringLiteral("pass_through")
                                   && !subtreeContainsTransientPreview(index);
        const quint64 cacheSignature = cacheEligible ? subtreeCacheSignature(index) : 0;
        if (cacheEligible) {
            const auto found = m_groupCompositeCaches.constFind(index);
            if (found != m_groupCompositeCaches.constEnd()
                && found->signature == cacheSignature && !found->image.isNull()) {
                return found->image;
            }
        }
        std::function<void(int, QImage &)> compositeEntry;
        compositeEntry = [&](int child, QImage &target) {
            const RasterLayer &entry = m_layers.at(child);
            if (!entry.visible) return;
            if (isGroupLayerType(entry.type) && entry.blendMode == QStringLiteral("pass_through")) {
                for (int nested = 0; nested < m_layers.size(); ++nested) if (m_layers.at(nested).parentIndex == child) compositeEntry(nested, target);
                return;
            }
            const QImage childImage = composeLayerSubtree(child);
            if (childImage.isNull()) return;
            QPainter painter(&target);
            painter.setCompositionMode(compositionModeForBlend(entry.blendMode));
            painter.setOpacity(qBound(0.0, entry.opacityPercent / 100.0, 1.0));
            painter.drawImage(QPoint(0, 0), childImage);
        };
        for (int child = 0; child < m_layers.size(); ++child) if (m_layers.at(child).parentIndex == index) compositeEntry(child, result);
        if (layer.maskEnabled && !layer.maskImage.isNull()) {
            QImage mask = layer.maskImage.convertToFormat(QImage::Format_Grayscale8);
            if (mask.size() != result.size()) mask = mask.scaled(result.size(), Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
            for (int y = 0; y < result.height(); ++y) {
                QRgb *dst = reinterpret_cast<QRgb *>(result.scanLine(y));
                const uchar *maskLine = mask.constScanLine(y);
                for (int x = 0; x < result.width(); ++x) {
                    const int a = maskLine[x];
                    const QRgb src = dst[x];
                    dst[x] = qRgba((qRed(src) * a + 127) / 255, (qGreen(src) * a + 127) / 255,
                                   (qBlue(src) * a + 127) / 255, (qAlpha(src) * a + 127) / 255);
                }
            }
        }
        if (cacheEligible) {
            // Keep a bounded number of cached folders. Entries are keyed by a
            // content signature, so a changed child invalidates only itself
            // and its ancestor folders rather than the whole layer stack.
            if (m_groupCompositeCaches.size() > 48) m_groupCompositeCaches.clear();
            m_groupCompositeCaches.insert(index, {cacheSignature, result});
        }
        return result;
    }

    if (layer.type == QStringLiteral("text") || !layer.textElements.isEmpty()) {
        QPainter textPainter(&result);
        textPainter.setRenderHint(QPainter::Antialiasing, true);
        for (const RasterLayer::TextElement &element : std::as_const(layer.textElements)) {
            if (element.text.isEmpty()) {
                continue;
            }
            QFont font(element.fontFamily.isEmpty() ? QStringLiteral("Sans Serif") : element.fontFamily);
            font.setPixelSize(qMax(1, qRound(element.fontPixelSize)));
            font.setBold(element.bold);
            font.setItalic(element.italic);
            font.setUnderline(element.underline);
            textPainter.save();
            textPainter.translate(element.position);
            textPainter.rotate(element.rotationDegrees);
            textPainter.setFont(font);
            textPainter.setPen(element.color);
            const QRectF bounds(0.0, 0.0, qMax(1, m_documentSize.width()), qMax(1, m_documentSize.height()));
            textPainter.drawText(bounds, element.alignment | Qt::TextWordWrap, element.text);
            textPainter.restore();
        }
        return result;
    }

    QImage composedLayer = layer.image;
    if (m_nonAccumulatingStrokeActive && index == m_activeLayerIndex
        && !m_strokePreviewLayerImage.isNull()
        && m_strokePreviewLayerImage.size() == layer.image.size()
        && !m_maskPaintingEnabled) {
        composedLayer = m_strokePreviewLayerImage;
    }
    if (composedLayer.isNull()) return QImage();
    if (layer.maskEnabled && !layer.maskImage.isNull()) {
        const QImage &maskSource = (m_maskPaintingEnabled && m_nonAccumulatingStrokeActive
                                    && index == m_activeLayerIndex && !m_maskStrokePreviewImage.isNull())
                                       ? m_maskStrokePreviewImage : layer.maskImage;
        QImage mask = maskSource.convertToFormat(QImage::Format_Grayscale8);
        if (mask.size() != composedLayer.size()) mask = mask.scaled(composedLayer.size(), Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
        composedLayer = composedLayer.convertToFormat(QImage::Format_ARGB32_Premultiplied);
        for (int y = 0; y < composedLayer.height(); ++y) {
            QRgb *dst = reinterpret_cast<QRgb *>(composedLayer.scanLine(y));
            const uchar *maskLine = mask.constScanLine(y);
            for (int x = 0; x < composedLayer.width(); ++x) {
                const int a = maskLine[x];
                const QRgb src = dst[x];
                dst[x] = qRgba((qRed(src) * a + 127) / 255, (qGreen(src) * a + 127) / 255,
                               (qBlue(src) * a + 127) / 255, (qAlpha(src) * a + 127) / 255);
            }
        }
    }
    return composedLayer;
}

QImage DrawingCanvas::composeLayersRegion(const QRect &requestedRegion) const
{
    const QRect region = requestedRegion.intersected(QRect(QPoint(0, 0), m_documentSize));
    if (region.isEmpty()) return QImage();

    // This is the CPU equivalent of a texture-set tile compositor. It keeps
    // all blending semantics intact, but allocates only the pixels touched by
    // the brush rather than a document-sized intermediate image.
    const auto applyMask = [](QImage &image, const QImage &maskSource) {
        if (image.isNull() || maskSource.isNull()) return;
        QImage mask = maskSource.format() == QImage::Format_Grayscale8
                          ? maskSource : maskSource.convertToFormat(QImage::Format_Grayscale8);
        if (mask.size() != image.size()) {
            mask = mask.scaled(image.size(), Qt::IgnoreAspectRatio, Qt::SmoothTransformation);
        }
        for (int y = 0; y < image.height(); ++y) {
            QRgb *dst = reinterpret_cast<QRgb *>(image.scanLine(y));
            const uchar *alpha = mask.constScanLine(y);
            for (int x = 0; x < image.width(); ++x) {
                const int a = alpha[x];
                const QRgb px = dst[x];
                dst[x] = qRgba((qRed(px) * a + 127) / 255,
                                (qGreen(px) * a + 127) / 255,
                                (qBlue(px) * a + 127) / 255,
                                (qAlpha(px) * a + 127) / 255);
            }
        }
    };

    std::function<void(int, QImage &)> compositeEntry;
    compositeEntry = [&](int index, QImage &target) {
        if (index < 0 || index >= m_layers.size()) return;
        const RasterLayer &layer = m_layers.at(index);
        if (!layer.visible) return;

        if (isGroupLayerType(layer.type)) {
            if (layer.blendMode == QStringLiteral("pass_through")) {
                for (int child = 0; child < m_layers.size(); ++child) {
                    if (m_layers.at(child).parentIndex == index) compositeEntry(child, target);
                }
                return;
            }

            QImage group(region.size(), QImage::Format_ARGB32_Premultiplied);
            if (!subtreeContainsTransientPreview(index)) {
                // Folders are cache boundaries: unrelated brush edits reuse
                // the already composited group and only crop the requested
                // tile for the parent stack.
                group = composeLayerSubtree(index).copy(region);
            } else {
                group.fill(Qt::transparent);
                for (int child = 0; child < m_layers.size(); ++child) {
                    if (m_layers.at(child).parentIndex == index) compositeEntry(child, group);
                }
                if (layer.maskEnabled && !layer.maskImage.isNull()) {
                    applyMask(group, layer.maskImage.copy(region));
                }
            }
            QPainter painter(&target);
            painter.setCompositionMode(compositionModeForBlend(layer.blendMode));
            painter.setOpacity(qBound(0.0, layer.opacityPercent / 100.0, 1.0));
            painter.drawImage(QPoint(0, 0), group);
            return;
        }

        QImage source;
        if ((layer.type == QStringLiteral("text") || !layer.textElements.isEmpty())) {
            // Text is comparatively rare. Reuse its existing renderer, then
            // crop the result so the common raster path remains tile-based.
            source = composeLayerSubtree(index).copy(region);
        } else {
            const QImage &fullImage = (m_nonAccumulatingStrokeActive
                                       && index == m_activeLayerIndex
                                       && !m_maskPaintingEnabled
                                       && !m_strokePreviewLayerImage.isNull())
                                          ? m_strokePreviewLayerImage : layer.image;
            source = fullImage.copy(region);
        }
        if (source.isNull()) return;
        if (layer.maskEnabled && !layer.maskImage.isNull()) {
            const QImage &mask = (m_maskPaintingEnabled && m_nonAccumulatingStrokeActive
                                  && index == m_activeLayerIndex && !m_strokePreviewLayerImage.isNull())
                                     ? m_strokePreviewLayerImage : layer.maskImage;
            applyMask(source, mask.copy(region));
        }
        QPainter painter(&target);
        painter.setCompositionMode(compositionModeForBlend(layer.blendMode));
        painter.setOpacity(qBound(0.0, layer.opacityPercent / 100.0, 1.0));
        painter.drawImage(QPoint(0, 0), source);
    };

    QImage result(region.size(), QImage::Format_ARGB32_Premultiplied);
    result.fill(Qt::transparent);
    for (int index = 0; index < m_layers.size(); ++index) {
        if (m_layers.at(index).parentIndex < 0) compositeEntry(index, result);
    }
    return result;
}

QImage DrawingCanvas::composeLayers() const
{
    if (m_layers.isEmpty()) return QImage();
    if (m_isDrawing && m_incrementalCompositeCacheActive
        && !m_pendingCompositeDirtyRect.isEmpty() && !m_composedCache.isNull()) {
        const QRect dirty = m_pendingCompositeDirtyRect;
        const QRegion regions = !m_pendingCompositeDamageRegion.isEmpty()
            ? m_pendingCompositeDamageRegion
            : (m_projectedStampProvider && !m_pendingProjectedCompositeRegion.isEmpty()
                ? m_pendingProjectedCompositeRegion : QRegion(dirty));
        if (!m_projectedStampProvider) {
            m_2dPerfCompositeRegions += regions.rectCount();
            for (const QRect &region : regions)
                m_2dPerfCompositePixels += static_cast<quint64>(region.width()) * region.height();
        }
        {
            // Detach once per coalesced paint event, then replace only the
            // changed tile. Groups, masks and blend modes are all evaluated by
            // composeLayersRegion(), so this is pixel-equivalent to a full
            // stack rebuild.
            QImage updated = m_composedCache.copy();
            QPainter painter(&updated);
            painter.setCompositionMode(QPainter::CompositionMode_Source);
            for (const QRect &region : regions) {
                const QImage patch = composeLayersRegion(region);
                if (patch.isNull() || patch.size() != region.size()) return m_composedCache;
                painter.drawImage(region.topLeft(), patch);
            }
            painter.end();
            m_composedCache = updated;
            m_composedCacheRevision = m_contentRevision;
            m_pendingCompositeDirtyRect = QRect();
            m_pendingCompositeDamageRegion = QRegion();
            m_pendingProjectedCompositeRegion = QRegion();
        }
        return m_composedCache;
    }
    // The preview-background shortcut cannot preserve the ordering of layers
    // above the active layer. Compose with the preview substituted in-place so
    // 2D display and 3D uploads have the same correct layer order.
    const bool transientPreview = m_nonAccumulatingStrokeActive
                                  && !m_maskPaintingEnabled
                                  && !m_strokeCompositeBackground.isNull()
                                  && !m_strokeCompositeForeground.isNull();
    if (!transientPreview && m_composedCacheRevision == m_contentRevision && !m_composedCache.isNull()) {
        return m_composedCache;
    }
    if (transientPreview && !m_strokeCompositeBackground.isNull()
        && m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        QImage result = m_strokeCompositeBackground.copy();
        const QImage active = composeLayerSubtree(m_activeLayerIndex);
        if (!active.isNull()) {
            QPainter painter(&result);
            const RasterLayer &activeLayer = m_layers.at(m_activeLayerIndex);
            painter.setCompositionMode(compositionModeForBlend(activeLayer.blendMode));
            painter.setOpacity(qBound(0.0, activeLayer.opacityPercent / 100.0, 1.0));
            painter.drawImage(QPoint(0, 0), active);
            painter.setOpacity(1.0);
            painter.setCompositionMode(QPainter::CompositionMode_SourceOver);
            painter.drawImage(QPoint(0, 0), m_strokeCompositeForeground);
        }
        return result;
    }
    QImage result(m_documentSize, QImage::Format_ARGB32_Premultiplied);
    result.fill(Qt::transparent);
    QPainter painter(&result);
    painter.setRenderHint(QPainter::Antialiasing, false);
    for (int i = 0; i < m_layers.size(); ++i) {
        const RasterLayer &layer = m_layers.at(i);
        if (layer.parentIndex >= 0 || !layer.visible) continue;
        if (isGroupLayerType(layer.type) && layer.blendMode == QStringLiteral("pass_through")) {
            painter.end();
            std::function<void(int)> compositePassEntry;
            compositePassEntry = [&](int child) {
                const RasterLayer &entry = m_layers.at(child);
                if (!entry.visible) return;
                if (isGroupLayerType(entry.type) && entry.blendMode == QStringLiteral("pass_through")) {
                    for (int nested=0;nested<m_layers.size();++nested) if(m_layers.at(nested).parentIndex==child) compositePassEntry(nested);
                    return;
                }
                const QImage image = composeLayerSubtree(child);
                if (image.isNull()) return;
                QPainter draw(&result); draw.setCompositionMode(compositionModeForBlend(entry.blendMode));
                draw.setOpacity(qBound(0.0, entry.opacityPercent / 100.0, 1.0)); draw.drawImage(QPoint(0,0), image);
            };
            for (int child=0;child<m_layers.size();++child) if(m_layers.at(child).parentIndex==i) compositePassEntry(child);
            painter.begin(&result);
            continue;
        }
        const QImage composedLayer = composeLayerSubtree(i);
        if (composedLayer.isNull()) continue;
        painter.setCompositionMode(compositionModeForBlend(layer.blendMode));
        painter.setOpacity(qBound(0.0, layer.opacityPercent / 100.0, 1.0));
        painter.drawImage(QPoint(0, 0), composedLayer);
    }
    painter.end();
    if (!transientPreview) {
        m_composedCache = result;
        m_composedCacheRevision = m_contentRevision;
    }
    return result;
}

QImage DrawingCanvas::composeLayersForDisplay() const
{
    if (!m_suppressExternalStrokeDisplay || !m_externalUvStrokeActive
        || m_externalStrokeDisplayImage.isNull()) {
        return composeLayers();
    }
    return m_externalStrokeDisplayImage;
}

bool DrawingCanvas::canDrawFlatStrokeStackDirectly() const
{
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return false;
    }
    for (const RasterLayer &layer : m_layers) {
        // This path deliberately covers the common paint stack only. Any
        // feature whose pixels require an intermediate compositor continues
        // through the cached/full composition path below.
        if (layer.parentIndex >= 0 || layer.type != QStringLiteral("raster")
            || layer.maskEnabled || !layer.textElements.isEmpty()
            || layer.blendMode != QStringLiteral("normal")
            || !qFuzzyCompare(layer.opacityPercent, 100.0)) {
            return false;
        }
    }
    return true;
}

bool DrawingCanvas::isLayerEffectivelyVisible(int index) const
{
    int current = index;
    for (int depth = 0; depth < m_layers.size(); ++depth) {
        if (current < 0) return true;
        if (current >= m_layers.size()) return false;
        const RasterLayer &layer = m_layers.at(current);
        if (!layer.visible) return false;
        const int parent = layer.parentIndex;
        if (parent < 0) return true;
        if (parent == current) return false;
        current = parent;
    }
    return false;
}

QImage *DrawingCanvas::activeLayerImage()
{
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return nullptr;
    }
    if (m_maskPaintingEnabled && m_layers[m_activeLayerIndex].maskEnabled
        && !m_layers[m_activeLayerIndex].maskImage.isNull()) {
        return &m_layers[m_activeLayerIndex].maskImage;
    }
    return &m_layers[m_activeLayerIndex].image;
}

const QImage *DrawingCanvas::activeLayerImage() const
{
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return nullptr;
    }
    if (m_maskPaintingEnabled && m_layers[m_activeLayerIndex].maskEnabled
        && !m_layers[m_activeLayerIndex].maskImage.isNull()) {
        return &m_layers[m_activeLayerIndex].maskImage;
    }
    return &m_layers[m_activeLayerIndex].image;
}

QRect DrawingCanvas::canvasRect() const
{
    QRect r = rect().adjusted(m_canvasMargin, m_canvasMargin, -m_canvasMargin, -m_canvasMargin);
    if (r.width() < 16 || r.height() < 16) {
        r = rect().adjusted(4, 4, -4, -4);
    }
    return r;
}

QRect DrawingCanvas::documentDisplayRect() const
{
    const QRect preview = canvasRect();
    if (!m_tilingPreviewEnabled) {
        return preview;
    }
    const int tileWidth = qMax(1, preview.width() / 3);
    const int tileHeight = qMax(1, preview.height() / 3);
    return QRect(preview.left() + tileWidth,
                 preview.top() + tileHeight,
                 tileWidth,
                 tileHeight);
}

bool DrawingCanvas::selectionCanvasContainsWidgetPoint(const QPointF &widgetPoint) const
{
    const QRect hitRect = (m_tilingPreviewEnabled && m_selectionToolEnabled)
                              ? documentDisplayRect() : canvasRect();
    const QPointF unrotated = rotatePointAround(widgetPoint, canvasRect().center(), -m_viewRotationDegrees);
    return hitRect.contains(unrotated.toPoint());
}

QTransform DrawingCanvas::canvasToViewAlignedTransform() const
{
    const QPointF center((qMax(1, m_documentSize.width()) - 1) * 0.5,
                         (qMax(1, m_documentSize.height()) - 1) * 0.5);
    QTransform t;
    t.translate(center.x(), center.y());
    t.rotate(m_viewRotationDegrees);
    t.translate(-center.x(), -center.y());
    return t;
}

QTransform DrawingCanvas::viewAlignedToCanvasTransform() const
{
    const QPointF center((qMax(1, m_documentSize.width()) - 1) * 0.5,
                         (qMax(1, m_documentSize.height()) - 1) * 0.5);
    QTransform t;
    t.translate(center.x(), center.y());
    t.rotate(-m_viewRotationDegrees);
    t.translate(-center.x(), -center.y());
    return t;
}

QPointF DrawingCanvas::canvasToViewAlignedPoint(const QPointF &canvasPoint) const
{
    return canvasToViewAlignedTransform().map(canvasPoint);
}

QPointF DrawingCanvas::viewAlignedToCanvasPoint(const QPointF &viewPoint) const
{
    return viewAlignedToCanvasTransform().map(viewPoint);
}

QPainterPath DrawingCanvas::canvasToViewAlignedPath(const QPainterPath &path) const
{
    return canvasToViewAlignedTransform().map(path);
}

QPainterPath DrawingCanvas::viewAlignedToCanvasPath(const QPainterPath &path) const
{
    return viewAlignedToCanvasTransform().map(path);
}

QPointF DrawingCanvas::widgetToCanvasPoint(const QPointF &widgetPoint) const
{
    const QRect fullPreviewRect = canvasRect();
    const QRect previewRect = (m_tilingPreviewEnabled && m_selectionToolEnabled)
                                  ? documentDisplayRect() : fullPreviewRect;
    const QPointF unrotated = rotatePointAround(widgetPoint, fullPreviewRect.center(), -m_viewRotationDegrees);
    qreal nx = (unrotated.x() - previewRect.left()) / qMax(1, previewRect.width() - 1);
    qreal ny = (unrotated.y() - previewRect.top()) / qMax(1, previewRect.height() - 1);
    if (m_tilingPreviewEnabled && !m_selectionToolEnabled) {
        nx = std::fmod(nx * 3.0, 1.0);
        ny = std::fmod(ny * 3.0, 1.0);
        if (nx < 0.0) {
            nx += 1.0;
        }
        if (ny < 0.0) {
            ny += 1.0;
        }
    }
    qreal x = nx * qMax(1, m_documentSize.width() - 1);
    qreal y = ny * qMax(1, m_documentSize.height() - 1);
    return QPointF(x, y);
}

QPointF DrawingCanvas::canvasToWidgetPoint(const QPointF &canvasPoint) const
{
    const QRect artRect = documentDisplayRect();
    const qreal nx = canvasPoint.x() / qMax(1, m_documentSize.width() - 1);
    const qreal ny = canvasPoint.y() / qMax(1, m_documentSize.height() - 1);
    const QPointF base(
        artRect.left() + nx * qMax(1, artRect.width() - 1),
        artRect.top() + ny * qMax(1, artRect.height() - 1));
    return rotatePointAround(base, artRect.center(), m_viewRotationDegrees);
}

QPointF DrawingCanvas::canvasPointFromWidgetPoint(const QPointF &widgetPoint) const
{
    return widgetToCanvasPoint(widgetPoint);
}

QPointF DrawingCanvas::widgetPointFromCanvasPoint(const QPointF &canvasPoint) const
{
    return canvasToWidgetPoint(canvasPoint);
}

bool DrawingCanvas::floodFillActiveLayerAtCanvasPoint(const QPointF &canvasPoint,
                                                      const QColor &fillColor,
                                                      bool contiguous,
                                                      bool closeGaps,
                                                      int gapTolerance,
                                                      int expandPixels,
                                                      bool sampleAllLayers)
{
    if (!fillColor.isValid()) {
        return false;
    }
    if (m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()) {
        return false;
    }

    RasterLayer &layer = m_layers[m_activeLayerIndex];
    const bool editingMask = m_maskPaintingEnabled;
    QImage *targetImage = editingMask ? &layer.maskImage : &layer.image;
    if (isRasterLayerEffectivelyLocked(m_activeLayerIndex) || !isLayerEffectivelyVisible(m_activeLayerIndex)
        || (!editingMask && (isGroupLayerType(layer.type) || isFillLayerType(layer.type)))
        || targetImage->isNull()) {
        return false;
    }

    const int width = targetImage->width();
    const int height = targetImage->height();
    if (width <= 0 || height <= 0) {
        return false;
    }

    const int seedX = qBound(0, static_cast<int>(std::floor(canvasPoint.x())), width - 1);
    const int seedY = qBound(0, static_cast<int>(std::floor(canvasPoint.y())), height - 1);
    const QPoint seed(seedX, seedY);
    if (m_hasSelectionRegion && !m_selectionClipRegion.contains(seed)) {
        return false;
    }

    // A mask fill always compares mask values.  Sampling the painted layer
    // stack here would make a mask-mode bucket write to data it did not test.
    QImage referenceImage = (!editingMask && sampleAllLayers)
                                ? composeLayers().convertToFormat(QImage::Format_ARGB32_Premultiplied)
                                : targetImage->convertToFormat(QImage::Format_ARGB32_Premultiplied);
    if (referenceImage.isNull() || referenceImage.width() != width || referenceImage.height() != height) {
        return false;
    }

    const QRgb seedRgb = referenceImage.pixel(seedX, seedY);
    const int tolerance = closeGaps ? qBound(0, gapTolerance, 255) : 0;
    auto colorMatches = [&](QRgb src) {
        return std::abs(qRed(src) - qRed(seedRgb)) <= tolerance
               && std::abs(qGreen(src) - qGreen(seedRgb)) <= tolerance
               && std::abs(qBlue(src) - qBlue(seedRgb)) <= tolerance
               && std::abs(qAlpha(src) - qAlpha(seedRgb)) <= tolerance;
    };

    auto canConsiderPoint = [&](int x, int y) {
        if (x < 0 || x >= width || y < 0 || y >= height) {
            return false;
        }
        if (m_hasSelectionRegion && !m_selectionClipRegion.contains(QPoint(x, y))) {
            return false;
        }
        return true;
    };

    QByteArray fillMask(width * height, 0);
    auto idxOf = [width](int x, int y) {
        return y * width + x;
    };

    if (contiguous) {
        QVector<int> stack;
        stack.reserve(width * height / 8);
        if (!colorMatches(referenceImage.pixel(seedX, seedY))) {
            return false;
        }
        stack.push_back(idxOf(seedX, seedY));

        while (!stack.isEmpty()) {
            const int idx = stack.back();
            stack.pop_back();
            if (fillMask[idx]) {
                continue;
            }
            const int y = idx / width;
            const int x = idx - y * width;
            if (!canConsiderPoint(x, y)) {
                continue;
            }
            if (!colorMatches(referenceImage.pixel(x, y))) {
                continue;
            }

            fillMask[idx] = 1;
            const int nx4[4] = {x - 1, x + 1, x, x};
            const int ny4[4] = {y, y, y - 1, y + 1};
            for (int i = 0; i < 4; ++i) {
                if (canConsiderPoint(nx4[i], ny4[i])) {
                    const int ni = idxOf(nx4[i], ny4[i]);
                    if (!fillMask[ni]) {
                        stack.push_back(ni);
                    }
                }
            }
            if (closeGaps) {
                for (int oy = -1; oy <= 1; ++oy) {
                    for (int ox = -1; ox <= 1; ++ox) {
                        if (ox == 0 && oy == 0) {
                            continue;
                        }
                        const int nx = x + ox;
                        const int ny = y + oy;
                        if (canConsiderPoint(nx, ny)) {
                            const int ni = idxOf(nx, ny);
                            if (!fillMask[ni]) {
                                stack.push_back(ni);
                            }
                        }
                    }
                }
            }
        }
    } else {
        for (int y = 0; y < height; ++y) {
            const QRgb *scan = reinterpret_cast<const QRgb *>(referenceImage.constScanLine(y));
            for (int x = 0; x < width; ++x) {
                if (!canConsiderPoint(x, y)) {
                    continue;
                }
                if (colorMatches(scan[x])) {
                    fillMask[idxOf(x, y)] = 1;
                }
            }
        }
    }

    int expand = qMax(0, expandPixels);
    while (expand-- > 0) {
        QByteArray nextMask = fillMask;
        for (int y = 0; y < height; ++y) {
            for (int x = 0; x < width; ++x) {
                const int idx = idxOf(x, y);
                if (!fillMask[idx]) {
                    continue;
                }
                for (int oy = -1; oy <= 1; ++oy) {
                    for (int ox = -1; ox <= 1; ++ox) {
                        if (ox == 0 && oy == 0) {
                            continue;
                        }
                        const int nx = x + ox;
                        const int ny = y + oy;
                        if (!canConsiderPoint(nx, ny)) {
                            continue;
                        }
                        nextMask[idxOf(nx, ny)] = 1;
                    }
                }
            }
        }
        fillMask = nextMask;
    }

    const int srcA = qBound(0, fillColor.alpha(), 255);
    const QRgb fillRgb = qRgba(qGray(fillColor.rgb()), qGray(fillColor.rgb()), qGray(fillColor.rgb()), 255);
    bool changed = false;
    const QImage sourceImage = targetImage->convertToFormat(QImage::Format_ARGB32_Premultiplied);
    for (int y = 0; y < height; ++y) {
        const QRgb *scan = reinterpret_cast<const QRgb *>(sourceImage.constScanLine(y));
        for (int x = 0; x < width; ++x) {
            if (!fillMask[idxOf(x, y)]) {
                continue;
            }

            const QRgb old = scan[x];
            if (!editingMask && layer.transparentPixelsLocked && qAlpha(old) == 0) {
                continue;
            }

            QRgb next = old;
            if (editingMask) {
                next = fillRgb;
            } else if (layer.transparentPixelsLocked) {
                const int oldA = qAlpha(old);
                const int inv = 255 - srcA;
                const int r = (qRed(old) * inv + fillColor.red() * srcA + 127) / 255;
                const int g = (qGreen(old) * inv + fillColor.green() * srcA + 127) / 255;
                const int b = (qBlue(old) * inv + fillColor.blue() * srcA + 127) / 255;
                next = qRgba(r, g, b, oldA);
            } else {
                next = fillColor.rgba();
            }

            if (next != old) {
                changed = true;
                break;
            }
        }
        if (changed) {
            break;
        }
    }

    if (!changed) {
        return false;
    }

    if (editingMask && onMaskPaintAboutToChange) onMaskPaintAboutToChange();
    pushUndoHistoryState(QStringLiteral("bucket"));
    QImage img = sourceImage.copy();
    for (int y = 0; y < height; ++y) {
        QRgb *scan = reinterpret_cast<QRgb *>(img.scanLine(y));
        for (int x = 0; x < width; ++x) {
            if (!fillMask[idxOf(x, y)]) {
                continue;
            }

            const QRgb old = scan[x];
            if (!editingMask && layer.transparentPixelsLocked && qAlpha(old) == 0) {
                continue;
            }

            if (editingMask) {
                scan[x] = fillRgb;
            } else if (layer.transparentPixelsLocked) {
                const int oldA = qAlpha(old);
                const int inv = 255 - srcA;
                const int r = (qRed(old) * inv + fillColor.red() * srcA + 127) / 255;
                const int g = (qGreen(old) * inv + fillColor.green() * srcA + 127) / 255;
                const int b = (qBlue(old) * inv + fillColor.blue() * srcA + 127) / 255;
                scan[x] = qRgba(r, g, b, oldA);
            } else {
                scan[x] = fillColor.rgba();
            }
        }
    }
    // Re-enter through the container so its copy-on-write storage detaches from
    // the history snapshot before the current layer image is changed. Writing
    // through `layer` here would mutate the shared snapshot too.
    if (editingMask) {
        m_layers[m_activeLayerIndex].maskImage = img.convertToFormat(QImage::Format_Grayscale8);
        m_layers[m_activeLayerIndex].meshMaskFaceIndices.clear();
    } else {
        m_layers[m_activeLayerIndex].image = img;
    }
    bumpContentRevision();
    if (onLayerStackChanged) {
        onLayerStackChanged();
    }
    update();
    return true;
}

void DrawingCanvas::applySystemCursorForBrushCursor(bool force)
{
    if (!m_showBrushCursor && m_idleToolCursorEnabled) {
        setCursor(m_idleToolCursor);
        return;
    }
    const Qt::CursorShape desired = m_showBrushCursor ? Qt::BlankCursor : Qt::ArrowCursor;
    if (!force && cursor().shape() == desired) {
        return;
    }
    setCursor(desired);
}

void DrawingCanvas::setIdleToolCursor(const QCursor &cursor, bool enabled)
{
    m_idleToolCursor = cursor;
    m_idleToolCursorEnabled = enabled;
    applySystemCursorForBrushCursor(true);
}

void DrawingCanvas::startQuickAdjustFromGlobalCursor(bool opacity)
{
    beginQuickAdjust(opacity ? QuickAdjustMode::BrushOpacity : QuickAdjustMode::BrushSize);
}

bool DrawingCanvas::isQuickAdjustActive() const
{
    return m_quickAdjustMode != QuickAdjustMode::None;
}

void DrawingCanvas::finishQuickAdjustFromGlobalPosition(const QPointF &globalPosition, bool commit)
{
    if (!isQuickAdjustActive()) return;
    if (commit) {
        updateQuickAdjustFromWidgetPoint(mapFromGlobal(globalPosition.toPoint()));
        commitQuickAdjust();
    } else {
        cancelQuickAdjust();
    }
}

void DrawingCanvas::setBrushCursorVisible(bool visible)
{
    m_showBrushCursor = visible;
    applySystemCursorForBrushCursor(true);
}

void DrawingCanvas::forceHideBrushCursor()
{
    const bool wasVisible = m_showBrushCursor;
    m_showBrushCursor = false;
    applySystemCursorForBrushCursor(true);
    if (wasVisible) {
        update();
    }
}

void DrawingCanvas::setBrushCursorFromWidgetPoint(const QPointF &widgetPoint, qreal pressure)
{
    if (!m_quickAdjustEnabled) {
        if (m_showBrushCursor) {
            setBrushCursorVisible(false);
            if (!m_isDrawing) {
                update();
            }
        }
        return;
    }

    const bool inside = canvasRect().contains(widgetPoint.toPoint());
    if (!inside) {
        if (m_showBrushCursor) {
            setBrushCursorVisible(false);
            if (!m_isDrawing) {
                update();
            }
        } else {
            applySystemCursorForBrushCursor(true);
        }
        return;
    }

    const bool wasVisible = m_showBrushCursor;
    const QPointF prevPoint = m_brushCursorCanvasPoint;
    const qreal prevPressure = m_brushCursorPressure;
    setBrushCursorVisible(true);
    m_brushCursorCanvasPoint = widgetToCanvasPoint(widgetPoint);
    m_brushCursorWidgetPoint = widgetPoint;
    m_brushCursorPressure = qBound(0.05, pressure, 1.0);

    // While drawing, stroke updates already repaint. Avoid duplicate repaint per input event.
    if (m_isDrawing) {
        return;
    }

    const bool movedEnough = !wasVisible
                            || std::abs(prevPoint.x() - m_brushCursorCanvasPoint.x()) > 0.25
                            || std::abs(prevPoint.y() - m_brushCursorCanvasPoint.y()) > 0.25
                            || std::abs(prevPressure - m_brushCursorPressure) > 0.01;
    if (movedEnough) {
        update();
    }
}

bool DrawingCanvas::updateColorPickerPreviewFromWidgetPoint(const QPointF &widgetPoint,
                                                            Qt::KeyboardModifiers modifiers,
                                                            bool activateIfPossible,
                                                            bool tabletInput)
{
    if (m_selectionToolEnabled || m_quickAdjustMode != QuickAdjustMode::None) {
        if (m_colorPickerPreviewActive) {
            m_colorPickerPreviewActive = false;
            m_colorPickerPreviewValid = false;
            applySystemCursorForBrushCursor(true);
            update();
        }
        return false;
    }

    const bool altHeld = modifiers.testFlag(Qt::AltModifier);
    const bool inside = canvasRect().contains(widgetPoint.toPoint());
    const bool canSample = !canSampleColorProvider || canSampleColorProvider();
    const bool shouldBeActive = activateIfPossible && altHeld && inside && canSample;

    if (!shouldBeActive) {
        if (m_colorPickerPreviewActive) {
            m_colorPickerPreviewActive = false;
            m_colorPickerPreviewValid = false;
            applySystemCursorForBrushCursor(true);
            update();
        }
        return false;
    }

    if (!m_colorPickerPreviewActive) {
        m_colorPickerPreviewBaseColor = m_brushInkColor;
    }

    m_colorPickerPreviewActive = true;
    m_colorPickerPreviewTabletInput = tabletInput;
    m_colorPickerPreviewWidgetPoint = widgetPoint;
    m_colorPickerPreviewSampleActiveLayer = modifiers.testFlag(Qt::ShiftModifier);

    const QPointF canvasPoint = widgetToCanvasPoint(widgetPoint);
    QColor sampled;
    const bool sampledOk = m_colorPickerPreviewSampleActiveLayer
                               ? sampleActiveLayerColorAtCanvasPoint(canvasPoint, &sampled)
                               : sampleCompositedColorAtCanvasPoint(canvasPoint, &sampled);
    m_colorPickerPreviewValid = sampledOk;
    if (sampledOk) {
        m_colorPickerPreviewHoverColor = sampled;
    }

    setBrushCursorVisible(false);
    setCursor(colorPickerCursor());
    update();
    return true;
}

void DrawingCanvas::updateSelectionInteractionCursor(const QPointF &widgetPoint, Qt::KeyboardModifiers modifiers)
{
    if (!m_selectionToolEnabled) {
        return;
    }

    if (!canvasRect().contains(widgetPoint.toPoint()) && !isFreeTransformMode()) {
        setCursor(Qt::ArrowCursor);
        return;
    }

    const QPointF canvasPoint = widgetToCanvasPoint(widgetPoint);
    const QPointF viewPoint = canvasToViewAlignedPoint(canvasPoint);

    if (isFreeTransformMode() && hasSelectionRegion()) {
        if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Rotate) {
            setCursor(freeTransformRotateCursor());
            return;
        }
        if (m_freeTransformInteractionMode == FreeTransformInteractionMode::Scale
            && m_freeTransformActiveHandle >= 0) {
            setCursor(freeTransformHandleCursorShape(m_freeTransformActiveHandle));
            return;
        }
        if (m_freeTransformInteractionMode != FreeTransformInteractionMode::None) {
            setCursor(Qt::ClosedHandCursor);
            return;
        }

        const int hoveredHandle = freeTransformHandleAt(viewPoint);
        if (hoveredHandle >= 0) {
            setCursor(freeTransformHandleCursorShape(hoveredHandle));
            return;
        }
        if (freeTransformPointNearRotationRing(viewPoint)) {
            setCursor(freeTransformRotateCursor());
            return;
        }
        if (freeTransformPointNearPivot(viewPoint)) {
            setCursor(Qt::SizeAllCursor);
            return;
        }
        if (freeTransformPointInside(viewPoint)) {
            setCursor(Qt::OpenHandCursor);
            return;
        }
    }

    if (m_selectionTranslationActive || m_layerTranslationActive) {
        setCursor(Qt::ClosedHandCursor);
        return;
    }

    if (hasSelectionRegion()) {
        const bool ctrlMove = modifiers.testFlag(Qt::ControlModifier) && m_selectionClipRegion.contains(canvasPoint.toPoint());
        const bool edgeMove = isNearSelectionBoundary(canvasPoint);
        if (ctrlMove || edgeMove) {
            setCursor(Qt::OpenHandCursor);
            return;
        }
    }

    if (modifiers.testFlag(Qt::AltModifier)) {
        setCursor(selectionSubtractCursor());
        return;
    }
    if (modifiers.testFlag(Qt::ShiftModifier)) {
        setCursor(selectionAddCursor());
        return;
    }

    setCursor(Qt::CrossCursor);
}

QColor DrawingCanvas::workspaceColor() const
{
    return m_canvasBackgroundColor;
}

DrawingTestWidget::DrawingTestWidget(QWidget *parent)
    : QWidget(parent)
{
    auto *rootLayout = new QVBoxLayout(this);
    rootLayout->setContentsMargins(10, 10, 10, 10);
    rootLayout->setSpacing(10);

    auto *toolbarLayout = new QHBoxLayout();
    toolbarLayout->setSpacing(8);

    m_brushButton = new QPushButton(L("canvas.tool.brush", "브러시"));
    m_eraserButton = new QPushButton(L("canvas.tool.eraser", "지우개"));
    auto *clearButton = new QPushButton(L("canvas.tool.clear", "초기화"));

    m_brushButton->setCheckable(true);
    m_eraserButton->setCheckable(true);
    m_brushButton->setChecked(true);

    m_infoLabel = new QLabel(L("canvas.info_default", "원형 + 필압 + 간격 0% + 하드니스 100%"));
    m_infoLabel->setStyleSheet("color: #aefb4f;");

    toolbarLayout->addWidget(m_brushButton);
    toolbarLayout->addWidget(m_eraserButton);
    toolbarLayout->addWidget(clearButton);
    toolbarLayout->addSpacing(14);
    toolbarLayout->addWidget(m_infoLabel);
    toolbarLayout->addStretch(1);

    m_canvas = new DrawingCanvas();

    rootLayout->addLayout(toolbarLayout);
    rootLayout->addWidget(m_canvas, 1);

    connect(m_brushButton, &QPushButton::clicked, this, [this]() {
        m_canvas->setTool(DrawingCanvas::Tool::Brush);
        updateToolUi();
    });

    connect(m_eraserButton, &QPushButton::clicked, this, [this]() {
        m_canvas->setTool(DrawingCanvas::Tool::Eraser);
        updateToolUi();
    });

    connect(clearButton, &QPushButton::clicked, this, [this]() {
        m_canvas->clearCanvas();
    });

    updateToolUi();
}

void DrawingTestWidget::updateToolUi()
{
    const bool brushActive = m_brushButton->isChecked() || !m_eraserButton->isChecked();

    if (brushActive) {
        m_brushButton->setChecked(true);
        m_eraserButton->setChecked(false);
    } else {
        m_brushButton->setChecked(false);
        m_eraserButton->setChecked(true);
    }

    const QString activeStyle = QString("background: %1; border: 1px solid %2; color: %3;")
                                   .arg(m_activeButtonBg.name())
                                   .arg(m_activeButtonBorder.name())
                                   .arg(m_activeButtonText.name());
    const QString normalStyle = "";

    m_brushButton->setStyleSheet(m_brushButton->isChecked() ? activeStyle : normalStyle);
    m_eraserButton->setStyleSheet(m_eraserButton->isChecked() ? activeStyle : normalStyle);
    m_infoLabel->setStyleSheet(QString("color: %1;").arg(m_infoTextColor));
}

DrawingCanvas *DrawingTestWidget::canvas() const
{
    return m_canvas;
}

void DrawingTestWidget::setBrushTool()
{
    m_canvas->setTool(DrawingCanvas::Tool::Brush);
    m_brushButton->setChecked(true);
    m_eraserButton->setChecked(false);
    updateToolUi();
}

void DrawingTestWidget::setEraserTool()
{
    m_canvas->setTool(DrawingCanvas::Tool::Eraser);
    m_brushButton->setChecked(false);
    m_eraserButton->setChecked(true);
    updateToolUi();
}

void DrawingTestWidget::setBrushSize(int size)
{
    m_canvas->setBrushSize(size);
}

void DrawingTestWidget::setBrushHardness(int hardnessPercent)
{
    m_canvas->setHardness(hardnessPercent);
}

void DrawingTestWidget::setBrushSpacing(int spacingPercent)
{
    m_canvas->setSpacing(spacingPercent);
}

void DrawingTestWidget::setBrushOpacity(int opacityPercent)
{
    m_canvas->setOpacity(opacityPercent);
}

void DrawingTestWidget::setBrushFlow(int flowPercent)
{
    m_canvas->setFlow(flowPercent);
}

void DrawingTestWidget::setBrushRoundness(int roundnessPercent)
{
    m_canvas->setRoundness(roundnessPercent);
}

void DrawingTestWidget::setBrushAngle(int angleDegrees)
{
    m_canvas->setAngle(angleDegrees);
}

void DrawingTestWidget::setBrushRandomAngle(int angleDegrees)
{
    m_canvas->setRandomAngle(angleDegrees);
}

void DrawingTestWidget::setBrushTipCircle()
{
    m_canvas->setBrushTipCircle();
}

void DrawingTestWidget::setBrushTipTexture(const QImage &textureImage)
{
    m_canvas->setBrushTipTexture(textureImage);
}

bool DrawingCanvas::insertRasterText(const QPointF &canvasPoint, const QString &text,
                                     const QFont &font, const QColor &color)
{
    if (text.isEmpty() || m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()
        || isGroupLayerType(m_layers.at(m_activeLayerIndex).type)
        || isRasterLayerEffectivelyLocked(m_activeLayerIndex)
        || !isRasterLayerEffectivelyVisible(m_activeLayerIndex)) {
        return false;
    }

    QImage source = m_layers.at(m_activeLayerIndex).image;
    if (source.isNull()) {
        source = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
        source.fill(Qt::transparent);
    }
    pushUndoHistoryState(QStringLiteral("text"));
    QImage result = source.copy();
    {
        QPainter painter(&result);
        painter.setRenderHint(QPainter::Antialiasing, true);
        painter.setRenderHint(QPainter::TextAntialiasing, true);
        painter.setFont(font);
        const int gray = qGray(color.rgb());
        painter.setPen(m_grayscaleOnly ? QColor(gray, gray, gray, color.alpha()) : color);
        const QFontMetricsF metrics(font);
        painter.drawText(QPointF(canvasPoint.x(), canvasPoint.y() + metrics.ascent()), text);
    }
    m_layers[m_activeLayerIndex].image = result;
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
    return true;
}

bool DrawingCanvas::insertRasterRichText(const QPointF &canvasPoint, const QString &html,
                                         qreal textWidth, qreal displayScale,
                                         const QColor &defaultColor)
{
    if (html.isEmpty() || m_activeLayerIndex < 0 || m_activeLayerIndex >= m_layers.size()
        || isGroupLayerType(m_layers.at(m_activeLayerIndex).type)
        || isRasterLayerEffectivelyLocked(m_activeLayerIndex)
        || !isRasterLayerEffectivelyVisible(m_activeLayerIndex)) return false;
    QImage source = m_layers.at(m_activeLayerIndex).image;
    if (source.isNull()) {
        source = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
        source.fill(Qt::transparent);
    }
    QTextDocument document;
    document.setDocumentMargin(0);
    document.setDefaultStyleSheet(QStringLiteral("body { color: %1; }").arg(defaultColor.name(QColor::HexArgb)));
    document.setHtml(html);
    const qreal safeScale = qMax<qreal>(0.01, displayScale);
    document.setTextWidth(qMax<qreal>(1.0, textWidth * safeScale));
    pushUndoHistoryState(QStringLiteral("text"));
    QImage result = source.copy();
    {
        QPainter painter(&result);
        painter.translate(canvasPoint);
        painter.scale(1.0 / safeScale, 1.0 / safeScale);
        document.drawContents(&painter);
    }
    m_layers[m_activeLayerIndex].image = result;
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
    return true;
}

bool DrawingCanvas::addTextElement(const RasterLayer::TextElement &element,
                                   const QString &layerName)
{
    if (element.text.trimmed().isEmpty()) return false;
    ensureLayers();

    int target = -1;
    if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
        const RasterLayer &active = m_layers.at(m_activeLayerIndex);
        if (active.type == QStringLiteral("text") && !isRasterLayerEffectivelyLocked(m_activeLayerIndex)
            && isRasterLayerEffectivelyVisible(m_activeLayerIndex)) {
            target = m_activeLayerIndex;
        }
    }

    pushUndoHistoryState(QStringLiteral("text-element"));
    if (target < 0) {
        RasterLayer layer;
        layer.layerId = QStringLiteral("text_%1").arg(m_layers.size() + 1);
        layer.name = layerName.trimmed().isEmpty() ? QStringLiteral("Text") : layerName.trimmed();
        layer.type = QStringLiteral("text");
        layer.image = QImage(m_documentSize, QImage::Format_ARGB32_Premultiplied);
        layer.image.fill(Qt::transparent);
        layer.visible = true;
        layer.opacityPercent = 100;
        layer.expanded = true;
        int insertIndex = m_layers.size();
        int parentIndex = -1;
        if (m_activeLayerIndex >= 0 && m_activeLayerIndex < m_layers.size()) {
            parentIndex = m_layers.at(m_activeLayerIndex).parentIndex;
            insertIndex = qBound(0, m_activeLayerIndex + 1, m_layers.size());
            for (int i = 0; i < m_layers.size(); ++i)
                if (m_layers[i].parentIndex >= insertIndex) ++m_layers[i].parentIndex;
            if (parentIndex >= insertIndex) ++parentIndex;
        }
        layer.parentIndex = qBound(-1, parentIndex, m_layers.size());
        m_layers.insert(insertIndex, layer);
        target = insertIndex;
        m_activeLayerIndex = target;
    }

    m_layers[target].textElements.push_back(element);
    bumpContentRevision();
    if (onLayerStackChanged) onLayerStackChanged();
    update();
    return true;
}

QRectF DrawingCanvas::textElementLocalBounds(const RasterLayer::TextElement &element) const
{
    QFont font(element.fontFamily.isEmpty() ? QStringLiteral("Sans Serif") : element.fontFamily);
    font.setPixelSize(qMax(1, qRound(element.fontPixelSize)));
    font.setBold(element.bold);
    font.setItalic(element.italic);
    font.setUnderline(element.underline);
    const QFontMetricsF metrics(font);
    const QRectF bounds = metrics.boundingRect(QRectF(0, 0,
                                                       qMax(1, m_documentSize.width()),
                                                       qMax(1, m_documentSize.height())),
                                               element.alignment | Qt::TextWordWrap,
                                               element.text);
    return QRectF(0, 0, qMax<qreal>(8.0, bounds.width()), qMax<qreal>(8.0, bounds.height()));
}

QRectF DrawingCanvas::textElementBounds(int layerIndex, int elementIndex) const
{
    if (layerIndex < 0 || layerIndex >= m_layers.size()
        || elementIndex < 0 || elementIndex >= m_layers.at(layerIndex).textElements.size()) {
        return QRectF();
    }
    const RasterLayer::TextElement &element = m_layers.at(layerIndex).textElements.at(elementIndex);
    const QRectF local = textElementLocalBounds(element);
    QTransform transform;
    transform.translate(element.position.x(), element.position.y());
    transform.rotate(element.rotationDegrees);
    return transform.mapRect(local);
}

bool DrawingCanvas::textElementAt(const QPointF &canvasPoint, int *layerIndex, int *elementIndex) const
{
    for (int layer = m_layers.size() - 1; layer >= 0; --layer) {
        const RasterLayer &entry = m_layers.at(layer);
        if (entry.type != QStringLiteral("text") || !isLayerEffectivelyVisible(layer)) continue;
        for (int element = entry.textElements.size() - 1; element >= 0; --element) {
            const RasterLayer::TextElement &value = entry.textElements.at(element);
            QTransform inverse;
            inverse.translate(value.position.x(), value.position.y());
            inverse.rotate(value.rotationDegrees);
            bool invertible = false;
            const QPointF localPoint = inverse.inverted(&invertible).map(canvasPoint);
            if (invertible && textElementLocalBounds(value).contains(localPoint)) {
                if (layerIndex) *layerIndex = layer;
                if (elementIndex) *elementIndex = element;
                return true;
            }
        }
    }
    return false;
}

bool DrawingCanvas::moveTextElement(int layerIndex, int elementIndex, const QPointF &delta)
{
    if (layerIndex < 0 || layerIndex >= m_layers.size() || elementIndex < 0
        || elementIndex >= m_layers.at(layerIndex).textElements.size()
        || isRasterLayerEffectivelyLocked(layerIndex)) return false;
    m_layers[layerIndex].textElements[elementIndex].position += delta;
    bumpContentRevision();
    update();
    return true;
}

bool DrawingCanvas::scaleTextElement(int layerIndex, int elementIndex, qreal factor)
{
    if (layerIndex < 0 || layerIndex >= m_layers.size() || elementIndex < 0
        || elementIndex >= m_layers.at(layerIndex).textElements.size()
        || isRasterLayerEffectivelyLocked(layerIndex)) return false;
    auto &element = m_layers[layerIndex].textElements[elementIndex];
    element.fontPixelSize = qBound<qreal>(1.0, element.fontPixelSize * factor, 4096.0);
    bumpContentRevision();
    update();
    return true;
}

bool DrawingCanvas::rotateTextElement(int layerIndex, int elementIndex, qreal degrees)
{
    if (layerIndex < 0 || layerIndex >= m_layers.size() || elementIndex < 0
        || elementIndex >= m_layers.at(layerIndex).textElements.size()
        || isRasterLayerEffectivelyLocked(layerIndex)) return false;
    auto &element = m_layers[layerIndex].textElements[elementIndex];
    element.rotationDegrees = std::fmod(element.rotationDegrees + degrees + 540.0, 360.0) - 180.0;
    bumpContentRevision();
    update();
    return true;
}

bool DrawingCanvas::editTextElement(int layerIndex, int elementIndex, QString *text,
                                    QString *fontFamily, qreal *fontPixelSize, QColor *color,
                                    bool *bold, bool *italic, bool *underline)
{
    if (layerIndex < 0 || layerIndex >= m_layers.size() || elementIndex < 0
        || elementIndex >= m_layers.at(layerIndex).textElements.size()) return false;
    const auto &element = m_layers.at(layerIndex).textElements.at(elementIndex);
    if (text) *text = element.text;
    if (fontFamily) *fontFamily = element.fontFamily;
    if (fontPixelSize) *fontPixelSize = element.fontPixelSize;
    if (color) *color = element.color;
    if (bold) *bold = element.bold;
    if (italic) *italic = element.italic;
    if (underline) *underline = element.underline;
    return true;
}

bool DrawingCanvas::updateTextElement(int layerIndex, int elementIndex,
                                      const RasterLayer::TextElement &element)
{
    if (element.text.trimmed().isEmpty() || layerIndex < 0 || layerIndex >= m_layers.size()
        || elementIndex < 0 || elementIndex >= m_layers.at(layerIndex).textElements.size()
        || isRasterLayerEffectivelyLocked(layerIndex)) return false;
    pushUndoHistoryState(QStringLiteral("text-edit"));
    m_layers[layerIndex].textElements[elementIndex] = element;
    bumpContentRevision();
    update();
    return true;
}

void DrawingCanvas::setTextElementSelection(int layerIndex, int elementIndex)
{
    m_selectedTextLayerIndex = layerIndex;
    m_selectedTextElementIndex = elementIndex;
    update();
}

void DrawingCanvas::clearTextElementSelection()
{
    m_selectedTextLayerIndex = -1;
    m_selectedTextElementIndex = -1;
    update();
}

void DrawingTestWidget::setBrushTipAntiAliasingEnabled(bool enabled)
{
    m_canvas->setBrushTipAntiAliasingEnabled(enabled);
}

void DrawingTestWidget::setSprayEnabled(bool enabled)
{
    m_canvas->setSprayEnabled(enabled);
}

void DrawingTestWidget::setSprayRangePercent(int percent)
{
    m_canvas->setSprayRangePercent(percent);
}

void DrawingTestWidget::setSprayDensity(int density)
{
    m_canvas->setSprayDensity(density);
}

void DrawingTestWidget::setSprayCenterDensity(int percent)
{
    m_canvas->setSprayCenterDensity(percent);
}

void DrawingTestWidget::setSprayParticleSize(int pixels)
{
    m_canvas->setSprayParticleSize(pixels);
}

void DrawingTestWidget::setSprayParticleRandomSize(int percent)
{
    m_canvas->setSprayParticleRandomSize(percent);
}

void DrawingTestWidget::setSprayParticleRotation(int degrees)
{
    m_canvas->setSprayParticleRotation(degrees);
}

void DrawingTestWidget::setSprayParticleRandomRotation(int degrees)
{
    m_canvas->setSprayParticleRandomRotation(degrees);
}

void DrawingTestWidget::setPressureSizeEnabled(bool enabled)
{
    m_canvas->setPressureSizeEnabled(enabled);
}

void DrawingTestWidget::setPressureOpacityEnabled(bool enabled)
{
    m_canvas->setPressureOpacityEnabled(enabled);
}

void DrawingTestWidget::setPressureSizeMinPercent(int percent)
{
    m_canvas->setPressureSizeMinPercent(percent);
}

void DrawingTestWidget::setPressureOpacityMinPercent(int percent)
{
    m_canvas->setPressureOpacityMinPercent(percent);
}

void DrawingTestWidget::setPressureSizeCurve(const QVector<qreal> &curve)
{
    m_canvas->setPressureSizeCurve(curve);
}

void DrawingTestWidget::setPressureOpacityCurve(const QVector<qreal> &curve)
{
    m_canvas->setPressureOpacityCurve(curve);
}

void DrawingTestWidget::clearCanvas()
{
    m_canvas->clearCanvas();
}

void DrawingTestWidget::setBrushInkColor(const QColor &color)
{
    m_canvas->setBrushInkColor(color);
}

void DrawingTestWidget::setThemeColors(const QColor &canvasBackground,
                                       const QColor &inkColor,
                                       const QString &infoTextColor,
                                       const QColor &activeButtonBg,
                                       const QColor &activeButtonBorder,
                                       const QColor &activeButtonText,
                                       int outlineStrength)
{
    m_canvas->setCanvasBackgroundColor(canvasBackground);
    m_canvas->setBrushInkColor(inkColor);

    const bool lightTheme = canvasBackground.lightnessF() > 0.60;
    const int strength = qBound(0, outlineStrength, 2);
    QColor outer = activeButtonBorder;
    QColor inner = activeButtonBg;
    QColor shadow = activeButtonBorder;

    if (lightTheme) {
        const int darkenBy[] = {114, 128, 146};
        const int lightenBy[] = {108, 118, 130};
        const int alphaBy[] = {24, 38, 58};
        outer = outer.darker(darkenBy[strength]);
        inner = inner.lighter(lightenBy[strength]);
        shadow.setAlpha(alphaBy[strength]);
    } else {
        const int outerBy[] = {102, 110, 124};
        const int innerBy[] = {124, 140, 160};
        const int alphaBy[] = {30, 50, 72};
        outer = outer.lighter(outerBy[strength]);
        inner = inner.lighter(innerBy[strength]);
        shadow.setAlpha(alphaBy[strength]);
    }

    m_canvas->setOutlineColors(outer, inner, shadow);
    m_infoTextColor = infoTextColor;
    m_activeButtonBg = activeButtonBg;
    m_activeButtonBorder = activeButtonBorder;
    m_activeButtonText = activeButtonText;
    updateToolUi();
}
